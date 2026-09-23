"""Semantic boundaries, content preservation and PDF failure handling."""
import json
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory
import unittest
from types import SimpleNamespace
from unittest.mock import patch
from contextlib import redirect_stdout
import io

import lean2html as renderer
import slides


class SlidesTest(unittest.TestCase):
    body = ('<h2 id="sec-Intro1.terms-types">1. 項と型</h2><p>説明。</p>'
            '<pre class="lean"><code>#check 3</code></pre>'
            '<pre class="quote"><code>3 : Nat</code></pre><p>自然数の型。</p>')
    config = {"version": 1, "rules": [{"at": {"section": "Intro1.terms-types", "code": "#check 3"},
                                        "id": "check-nat", "label": "#check 3"}]}

    def build(self, body):
        blocks = slides.blocks_from_html(body, "Intro1a")
        slides.apply_rules(blocks, self.config, "Intro1a")
        return slides.paginate(blocks, "Intro1a")

    def test_boundary_survives_inserted_paragraph_and_changed_section_number(self):
        first = self.build(self.body)
        edited = self.body.replace('1. 項と型', '9. 項と型').replace('<p>説明。</p>', '<p>新しい説明。</p><p>説明を改稿。</p>')
        second = self.build(edited)
        for pages in [first, second]:
            target = next(page for page in pages if page.id == 'intro1a-check-nat')
            self.assertEqual(target.steps[0][0].node.text, '#check 3')
            self.assertEqual(target.steps[1][0].node.text, '3 : Nat')

    def test_missing_or_ambiguous_selector_is_an_error(self):
        for body in [self.body.replace('#check 3', '#check 4'), self.body + '<pre class="lean">#check 3</pre>']:
            with self.assertRaisesRegex(ValueError, 'exactly once'):
                self.build(body)

    def test_quoted_declarations_do_not_match_live_code(self):
        blocks = slides.blocks_from_html('<pre class="quote">def x : Nat := 2</pre>'
                                         '<pre class="lean">def x : Nat := 2</pre>', 'T')
        self.assertEqual(sum(slides.matches(b, {'declaration':'x'}) for b in blocks), 1)

    def test_split_code_retains_every_character_and_highlighting(self):
        code = ''.join(f'  -- 長い説明 {i}\n  exact h{i}\n' for i in range(35))
        node = slides.Node('pre', {'class':'lean'}, [slides.Node('code', children=[slides.Node('span', {'class':'kw'}, [code])])])
        block = slides.Block(node, 'S', '見出し', key='long-code', source_text=code)
        pieces = slides.split_block(block)
        self.assertGreater(len(pieces), 1)
        self.assertEqual(''.join(p.node.text for p in pieces), code)
        for piece in pieces:
            self.assertIn('class="kw"', piece.node.render())
            self.assertLessEqual(slides.estimate(piece.node), slides.MAX_HEIGHT)

    def test_split_ordered_list_keeps_item_numbers(self):
        body = '<ol>' + ''.join('<li>' + ('説明。' * 50) + '</li>' for _ in range(4)) + '</ol>'
        block = slides.blocks_from_html(body, 'T')[0]
        pieces = slides.split_block(block)
        numbers = [int(piece.node.attrs['start']) for piece in pieces]
        self.assertEqual(sorted(set(numbers)), [1, 2, 3, 4])
        self.assertEqual(''.join(p.source_text for p in pieces), block.source_text)

    def test_optional_and_solutions_are_retained(self):
        body = self.body + '<aside class="note note--optional"><h3>補足</h3><p>補足の本文。</p></aside>' + \
               '<h3>練習</h3><p>問い。</p><details class="sol"><summary>解答 1</summary><p>答え。</p></details>'
        pages = self.build(body)
        self.assertTrue(any(page.kind == 'optional' for page in pages))
        self.assertEqual(len(pages[-1].answers), 1)
        printed = slides.slide_articles(pages, print_steps=True, chapter='T')
        self.assertIn('補足の本文。', printed)
        self.assertIn('答え。', printed)
        self.assertNotIn('<details', printed)

    def test_pdf_stages_do_not_reveal_output_early(self):
        page = next(p for p in self.build(self.body) if p.id == 'intro1a-check-nat')
        document = slides.FragmentParser(slides.slide_articles([page], print_steps=True, chapter='T')).root
        articles = [node for node in document.children if isinstance(node, slides.Node)]
        self.assertEqual(len(articles), 2)
        self.assertNotIn('3 : Nat', articles[0].text)
        self.assertIn('#check 3', articles[1].text)
        self.assertIn('3 : Nat', articles[1].text)

    def test_all_current_chapters_preserve_content_and_have_unique_page_ids(self):
        references = renderer.refs.analyze(renderer.SRC, renderer.CHAPTERS, renderer.SOL_FILES, renderer.parse)
        self.assertFalse(references.errors)
        for chapter in renderer.CHAPTERS:
            with self.subTest(chapter=chapter):
                body = renderer.render_chapter(chapter, renderer.parse(renderer.SRC / f'{chapter}.lean'), references.sections)
                blocks = slides.blocks_from_html(body, chapter)
                config = slides.CONFIG / f'{chapter}.json'
                if config.exists():
                    slides.apply_rules(blocks, json.loads(config.read_text()), chapter)
                pages = slides.paginate(blocks, chapter)
                self.assertEqual(len(pages), len({page.id for page in pages}))
                included = [b.source_text for p in pages for step in p.steps for b in step]
                # Solutions retain their own complete source trees; placement follows the exercise.
                self.assertEqual(sum(len(p.answers) for p in pages), sum(b.node.tag == 'details' for b in blocks))
                original = ''.join(b.source_text for b in blocks if b.node.tag != 'details')
                self.assertEqual(re.sub(r'\s', '', ''.join(included)), re.sub(r'\s', '', original))

    def test_failed_pdf_does_not_pass_due_to_existing_file(self):
        with TemporaryDirectory() as directory:
            path = Path(directory) / 'old.pdf'
            path.write_bytes(b'%PDF-old')
            with patch.object(renderer, 'find_chrome', return_value='/dummy/chrome'), \
                    patch('subprocess.Popen', return_value=SimpleNamespace(returncode=0, poll=lambda: 0, wait=lambda **kwargs: 0)):
                with self.assertRaisesRegex(RuntimeError, '生成に失敗'):
                    renderer.write_pdf('<html></html>', path)
            self.assertEqual(path.read_bytes(), b'%PDF-old')

    def test_links_preserve_external_urls_and_resolve_chapter_references(self):
        body = '<p><a href="#sec-T.one">同じ章</a><a href="ch1.html#sec-CH.one">別章</a>' + \
               '<a href="https://lean-lang.org/">外部</a></p>'
        pages = slides.paginate(slides.blocks_from_html(body, 'T'), 'T')
        screen = slides.html_page('T', 'Title', pages, ['T'])
        self.assertIn('href="../t.html#sec-T.one"', screen)
        self.assertIn('href="../ch1.html#sec-CH.one"', screen)
        self.assertIn('href="https://lean-lang.org/"', screen)
        printed = slides.slide_articles(pages, print_steps=True, chapter='T')
        self.assertIn('href="https://unaoya.github.io/lean-intro/t.html#sec-T.one"', printed)
        self.assertIn('href="https://lean-lang.org/"', printed)

    def test_cached_build_checks_inputs_and_actual_output_content(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            (root / '.lake').mkdir()
            output = root / 'generated.html'
            output.write_text('complete')
            cache = {'signature':'input-v1', 'outputs':{'generated.html':renderer.file_digest(output)}}
            (root / '.lake/textbook-build.json').write_text(json.dumps(cache))
            with patch.object(renderer, 'ROOT', root), \
                    patch.object(renderer, 'build_signature', return_value='input-v1') as signature, \
                    patch.object(renderer.refs, 'analyze', side_effect=RuntimeError('rebuilding')) as analyze, \
                    redirect_stdout(io.StringIO()):
                renderer.main(if_needed=True)
                analyze.assert_not_called()
                signature.return_value = 'input-v2'
                with self.assertRaisesRegex(RuntimeError, 'rebuilding'):
                    renderer.main(if_needed=True)
                signature.return_value = 'input-v1'
                output.write_text('changed')
                with self.assertRaisesRegex(RuntimeError, 'rebuilding'):
                    renderer.main(if_needed=True)
                output.unlink()
                with self.assertRaisesRegex(RuntimeError, 'rebuilding'):
                    renderer.main(if_needed=True)


if __name__ == '__main__':
    unittest.main()
