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
import editorial_slides


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

    def test_identical_definition_and_print_output_can_have_different_boundaries(self):
        blocks = slides.blocks_from_html('<pre class="lean">def x : Nat := 2</pre>'
                                        '<pre class="quote">def x : Nat :=\n2</pre>', 'T')
        slides.apply_rules(blocks, {'version':1, 'rules':[
            {'at':{'declaration':'x'}, 'id':'definition'},
            {'at':{'tag':'pre', 'class':'quote', 'text':'def x : Nat := 2'}, 'break':'keep'}]}, 'T')
        pages = slides.paginate(blocks, 'T')
        self.assertEqual(len(pages), 1)
        self.assertEqual(len(pages[0].steps), 1)
        self.assertEqual(len(pages[0].steps[0]), 2)

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

    def test_explicit_step_can_add_another_command_on_the_same_page(self):
        body = '<pre class="lean">#check 3</pre><pre class="quote">3 : Nat</pre>' + \
               '<pre class="lean">#eval 3</pre><pre class="quote">3</pre>'
        blocks = slides.blocks_from_html(body, 'T')
        slides.apply_rules(blocks, {'version':1, 'rules':[
            {'at':{'code':'#check 3'}, 'id':'example', 'layout':'compact'},
            {'at':{'code':'#eval 3'}, 'break':'step'}]}, 'T')
        pages = slides.paginate(blocks, 'T')
        self.assertEqual(len(pages), 1)
        self.assertEqual([s[0].node.text for s in pages[0].steps], ['#check 3', '3 : Nat', '#eval 3', '3'])

    def test_list_items_reveal_in_order_and_keep_numbers_in_pdf(self):
        body = '<p>説明。</p><ol start="3"><li>最初。</li><li>次。<ul><li>内側。</li></ul></li></ol>'
        blocks = slides.blocks_from_html(body, 'T')
        slides.apply_rules(blocks, {'version':1, 'rules':[
            {'at':{'tag':'ol','starts':'最初。'}, 'break':'step', 'reveal':'items'}]}, 'T')
        pages = slides.paginate(blocks, 'T')
        self.assertEqual(len(pages), 1)
        self.assertEqual(len(pages[0].steps), 3)
        self.assertEqual([s[0].node.attrs['start'] for s in pages[0].steps[1:]], ['3','4'])
        self.assertEqual(''.join(b.source_text for s in pages[0].steps for b in s),
                         ''.join(b.source_text for b in blocks))
        articles = [n for n in slides.FragmentParser(slides.slide_articles(
            pages, print_steps=True, chapter='T')).root.children if isinstance(n, slides.Node)]
        self.assertNotIn('最初。', articles[0].text)
        self.assertIn('最初。', articles[1].text)
        self.assertNotIn('次。', articles[1].text)
        self.assertIn('次。内側。', articles[2].text)
        self.assertIn('start="4"', articles[2].render())

    def test_automatic_flow_groups_explanation_commands_and_results(self):
        body = '<h3>項を調べる</h3><p>まず型を調べよう:</p>' + \
            '<pre class="lean">#check 3</pre><pre class="quote">3 : Nat</pre>' + \
            '<p>自然数の項である。</p><pre class="lean">#eval 3 + 4</pre><pre class="quote">7</pre>'
        pages = slides.paginate(slides.blocks_from_html(body, 'T'), 'T')
        self.assertEqual(len(pages), 1)
        self.assertEqual(pages[0].layout, 'compact')
        self.assertEqual([''.join(b.node.text for b in step) for step in pages[0].steps],
                         ['項を調べるまず型を調べよう:#check 3', '3 : Nat自然数の項である。', '#eval 3 + 4', '7'])

    def test_automatic_paragraphs_and_list_items_reveal_separately(self):
        body = '<p>導入。</p><p>次の説明。</p><ol start="4"><li>一つ目。</li><li>二つ目。</li></ol>'
        pages = slides.paginate(slides.blocks_from_html(body, 'T'), 'T')
        self.assertEqual(len(pages), 1)
        self.assertEqual([''.join(b.node.text for b in step) for step in pages[0].steps],
                         ['導入。', '次の説明。', '一つ目。', '二つ目。'])
        self.assertEqual([step[0].node.attrs['start'] for step in pages[0].steps[2:]], ['4', '5'])
        articles = [n for n in slides.FragmentParser(slides.slide_articles(
            pages, print_steps=True, chapter='T')).root.children if isinstance(n, slides.Node)]
        self.assertEqual(len(articles), 4)
        self.assertNotIn('二つ目。', articles[2].text)
        self.assertIn('二つ目。', articles[3].text)

    def test_explanation_after_quoted_syntax_is_a_new_step(self):
        body = '<p>宣言の形は:</p><pre class="quote">def 名前 : 型 := 項</pre><p>左辺に型を書く。</p>'
        pages = slides.paginate(slides.blocks_from_html(body, 'T'), 'T')
        self.assertEqual(len(pages), 1)
        self.assertEqual([''.join(b.node.text for b in step) for step in pages[0].steps],
                         ['宣言の形は:def 名前 : 型 := 項', '左辺に型を書く。'])

    def test_automatic_flow_moves_a_short_command_with_its_result(self):
        body = '<p>' + '長い説明。' * 44 + '</p>' + \
            '<pre class="lean">#check 3</pre><pre class="quote">3 : Nat</pre><p>結果の説明。</p>'
        pages = slides.paginate(slides.blocks_from_html(body, 'T'), 'T')
        self.assertEqual(len(pages), 2)
        self.assertEqual(''.join(b.node.text for s in pages[1].steps for b in s),
                         '#check 33 : Nat結果の説明。')
        self.assertTrue(all(p.height <= slides.height_limit(p.layout) for p in pages))

    def test_automatic_flow_keeps_headings_with_the_start_of_long_text(self):
        body = '<h3>新しい話題</h3><p>' + '長い説明。' * 100 + '</p>'
        pages = slides.paginate(slides.blocks_from_html(body, 'T'), 'T')
        self.assertEqual([b.node.tag for b in pages[0].steps[0]], ['h3', 'p'])
        self.assertTrue(all(p.height <= slides.height_limit(p.layout) for p in pages))

    def test_compact_page_and_keep_output_show_one_complete_example(self):
        body = '<pre class="lean">#check 3</pre><pre class="quote">3 : Nat</pre><p>' + '説明。' * 49 + '</p>'
        for layout, count in [('normal', 2), ('compact', 1)]:
            blocks = slides.blocks_from_html(body, 'T')
            slides.apply_rules(blocks, {'version':1, 'rules':[
                {'at':{'code':'#check 3'}, 'id':'check', 'layout':layout},
                {'at':{'tag':'pre', 'text':'3 : Nat'}, 'break':'keep'}]}, 'T')
            pages = slides.paginate(blocks, 'T')
            self.assertEqual(len(pages), count)
            self.assertEqual(len(pages[0].steps), 1)
            self.assertIn('3 : Nat', ''.join(b.node.text for b in pages[0].steps[0]))
            if layout == 'compact':
                self.assertEqual(len(pages[0].steps[0]), 3)
                self.assertLessEqual(pages[0].height, slides.MAX_HEIGHT)
                self.assertIn('data-layout="compact"', slides.slide_articles(pages, print_steps=True, chapter='T'))

    def test_build_omits_notes_by_default_and_can_include_them(self):
        body = self.body + \
            '<aside class="note note--optional"><h3>補足見出し</h3><p>補足本文。</p>' + \
            '<details class="sol"><summary>解答</summary><p>補足の解答。</p></details></aside>' + \
            '<aside class="note note--preview"><h3>先取り見出し</h3><p>先取り本文。</p></aside>' + \
            '<h3>練習</h3><p>本筋の問題。</p><details class="sol"><summary>解答</summary><p>本筋の解答。</p></details>'
        with TemporaryDirectory() as directory, redirect_stdout(io.StringIO()):
            out = Path(directory)
            for include in [False, True]:
                kwargs = {'include_notes': True} if include else {}
                document, pages = slides.build({'T':'Title'}, {'T':body}, ['T'], out, **kwargs)
                screen = (out / 'slides/t.html').read_text()
                for text in ['補足本文。', '補足の解答。', '先取り本文。']:
                    self.assertEqual(text in document, include)
                    self.assertEqual(text in screen, include)
                self.assertIn('本筋の解答。', document)
                self.assertIn('本筋の解答。', screen)
                self.assertEqual(any(p.kind != 'main' for p in pages['T']), include)
                self.assertEqual('class="optional-control" hidden' in screen, not include)

    def test_all_current_chapters_preserve_content_and_have_unique_page_ids(self):
        references = renderer.refs.analyze(renderer.SRC, renderer.CHAPTERS, renderer.SOL_FILES, renderer.parse)
        self.assertFalse(references.errors)
        for chapter in renderer.CHAPTERS:
            with self.subTest(chapter=chapter):
                body = renderer.render_chapter(chapter, renderer.parse(renderer.SRC / f'{chapter}.lean'), references.sections)
                blocks = slides.blocks_from_html(body, chapter)
                config = slides.CONFIG / f'{chapter}.json'
                if config.exists():
                    config = json.loads(config.read_text())
                    if config.get('version') == 2:
                        pages = editorial_slides.paginate(blocks, config, chapter, include_notes=True)
                        main_pages = editorial_slides.paginate(blocks, config, chapter)
                        self.assertTrue(all(p.editorial and p.kind == 'main' for p in main_pages))
                        rendered = ''.join(slides.FragmentParser(editorial_slides.render_content(p)).root.text
                                           for p in main_pages)
                        main_text = ''.join(b.source_text for b in blocks if b.kind == 'main')
                        self.assertEqual(re.sub(r'\s', '', rendered), re.sub(r'\s', '', main_text))
                    else:
                        slides.apply_rules(blocks, config, chapter)
                        pages = slides.paginate(blocks, chapter)
                else:
                    pages = slides.paginate(blocks, chapter)
                self.assertEqual(len(pages), len({page.id for page in pages}))
                for page in pages:
                    content = [b for step in page.steps for b in step]
                    self.assertFalse(len(content) == 1 and slides.is_exercise_heading(content[0]))
                included = [b.source_text for p in pages for step in p.steps for b in step]
                # Exercise answers are revealed immediately after their own question.
                included += [b.source_text for p in pages for b in p.answers]
                original = ''.join(b.source_text for b in blocks)
                self.assertEqual(re.sub(r'\s', '', ''.join(included)), re.sub(r'\s', '', original))

    def test_short_exercise_and_answer_share_page_with_separate_reveal(self):
        body = '<h3>✏ 練習</h3><ol start="28" data-exercise="28"><li>問い。</li></ol>' + \
            '<details class="sol" data-exercise="28"><summary>解答 28</summary><pre class="lean">#check 3</pre></details>' + \
            '<ol start="29" data-exercise="29"><li>次の問い。</li></ol>' + \
            '<details class="sol" data-exercise="29"><summary>解答 29</summary><p>次の答え。</p></details>'
        pages = slides.paginate(slides.blocks_from_html(body, 'T'), 'T')
        self.assertEqual(len(pages), 2)
        self.assertEqual([len(p.steps) for p in pages], [2, 2])
        self.assertIn('問い。', ''.join(b.node.text for b in pages[0].steps[0]))
        self.assertEqual('解答 28#check 3', ''.join(b.node.text for b in pages[0].steps[1]))
        articles = [n for n in slides.FragmentParser(slides.slide_articles(
            pages, print_steps=True, chapter='T')).root.children if isinstance(n, slides.Node)]
        self.assertEqual(len(articles), 4)
        self.assertNotIn('#check 3', articles[0].text)
        self.assertIn('問い。', articles[1].text)
        self.assertIn('#check 3', articles[1].text)
        self.assertIn('start="28"', articles[1].render())
        self.assertNotIn('次の問い。', articles[1].text)

    def test_long_answer_continues_before_next_question_without_orphan_label(self):
        answer = '\n'.join(f'-- 解答の行 {n}' for n in range(24))
        body = '<ol data-exercise="1"><li>' + '長い問い。' * 22 + '</li></ol>' + \
            '<details class="sol" data-exercise="1"><summary>解答 1</summary>' + \
            f'<pre class="lean">{answer}</pre></details>' + \
            '<ol data-exercise="2"><li>次の問い。</li></ol>'
        blocks = slides.blocks_from_html(body, 'T')
        pages = slides.paginate(blocks, 'T')
        self.assertGreater(len(pages), 3)
        all_text = ''.join(b.source_text for p in pages for step in p.steps for b in step)
        self.assertEqual(re.sub(r'\s', '', all_text), re.sub(r'\s', '', ''.join(b.source_text for b in blocks)))
        self.assertIn('次の問い。', ''.join(b.node.text for step in pages[-1].steps for b in step))
        for page in pages:
            self.assertLessEqual(page.height, slides.height_limit(page.layout))
            nodes = [b.node for step in page.steps for b in step]
            if any(n.text == '解答 1' for n in nodes):
                self.assertTrue(any(n.tag == 'pre' for n in nodes))

    def test_exercise_heading_shares_page_with_start_of_long_question(self):
        body = '<h3>✏ 練習</h3><ol start="99" data-exercise="99"><li>' + '長い問題の説明。' * 100 + '</li></ol>'
        blocks = slides.blocks_from_html(body, 'T')
        pages = slides.paginate(blocks, 'T')
        self.assertGreater(len(pages), 1)
        first = [b.node for step in pages[0].steps for b in step]
        self.assertEqual([n.tag for n in first], ['h3', 'ol'])
        self.assertIn('長い問題の説明。', first[1].text)
        text = ''.join(b.source_text for p in pages for step in p.steps for b in step)
        self.assertEqual(re.sub(r'\s', '', text), re.sub(r'\s', '', ''.join(b.source_text for b in blocks)))
        for page in pages:
            self.assertLessEqual(page.height, slides.height_limit(page.layout))

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

    def test_index_preserves_shared_introduction_and_links_to_the_right_edition(self):
        chapters = [ch for ch in renderer.CHAPTERS if ch not in renderer.SLIDE_EXCLUDED_CHAPTERS]
        titles = {ch: renderer.chapter_title(renderer.parse(renderer.SRC / f'{ch}.lean'))
                  for ch in renderer.CHAPTERS}
        body = renderer.lecture_index_html(titles, chapters)
        self.assertIn(renderer.introduction_html(), body)
        config = json.loads((slides.CONFIG / 'Index.json').read_text())
        pages = editorial_slides.paginate(slides.blocks_from_html(body, 'Index'), config, 'Index')
        rendered = ''.join(slides.FragmentParser(editorial_slides.render_content(p)).root.text for p in pages)
        self.assertEqual(re.sub(r'\s', '', rendered),
                         re.sub(r'\s', '', slides.FragmentParser(body).root.text))
        screen = slides.html_page('Index', renderer.SITE_TITLE, pages, ['Index', *chapters])
        tree = slides.FragmentParser(screen).root
        def descendants(node):
            for child in node.children:
                if isinstance(child, slides.Node):
                    yield child
                    yield from descendants(child)
        links = [n for n in descendants(tree) if n.tag == 'a']
        for ch in chapters:
            link = next(n for n in links if n.attrs.get('href') == ch.lower() + '.html')
            self.assertNotIn('target', link.attrs)
        for ch in ['06_Topology', '07_Exercises']:
            self.assertTrue(any(n.attrs.get('href') == '../' + ch.lower() + '.html' for n in links))
        exercises = [n for n in links if n.text == '発展演習']
        self.assertEqual(len(exercises), 1)
        self.assertEqual(exercises[0].attrs['href'], '../07_exercises.html')
        self.assertNotIn('sorry', body)
        self.assertNotIn('自由忘却随伴', body)
        self.assertNotIn('Ascoli の定理', body)
        self.assertIn('<option value="index.html" selected>はじめに</option>', screen)
        printed = slides.slide_articles(pages, print_steps=True, chapter='Index')
        self.assertIn('href="https://unaoya.github.io/lean-intro/slides/01_typesandterms.html"', printed)
        self.assertIn('href="https://unaoya.github.io/lean-intro/06_topology.html"', printed)

    def test_renamed_chapters_keep_pdf_references_and_legacy_slide_locations(self):
        chapters = ['01_TypesAndTerms', '02_Forall']
        bodies = {ch: '<p><a href="02_forall.html#sec-CH.implication">全称量化</a></p>' for ch in chapters}
        with patch.object(renderer, 'CHAPTERS', chapters):
            printed = renderer.pdf_html(dict.fromkeys(chapters, '章'), bodies)
        self.assertNotIn('02_forall.html#sec-', printed)
        self.assertIn('href="#sec-CH.implication"', printed)
        redirect = renderer.legacy_redirect_html('CH1', '02_Forall', slide=True)
        self.assertIn('fragment.startsWith("#ch1-")', redirect)
        self.assertIn('"#02_forall-" + fragment.slice(5)', redirect)
        self.assertIn('"02_forall.html" + location.search + fragment', redirect)

    def test_build_includes_index_in_screen_navigation_and_pdf(self):
        with TemporaryDirectory() as directory, redirect_stdout(io.StringIO()):
            out = Path(directory)
            document, pages = slides.build({'T': 'テスト章'}, {'T': self.body}, ['T'], out)
            self.assertEqual(list(pages), ['Index', 'T'])
            index = (out / 'slides/index.html').read_text()
            self.assertIn('class="slide"', index)
            self.assertIn('id="next"', index)
            self.assertIn('href="t.html"', index)
            chapter = (out / 'slides/t.html').read_text()
            self.assertIn('<option value="index.html">はじめに</option>', chapter)
            first = document.index('<article class="print-slide"')
            self.assertIn('はじめての Lean', document[first:document.index('</article>', first)])

    def test_cached_build_checks_inputs_and_actual_output_content(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            (root / '.lake').mkdir()
            output = root / 'generated.html'
            output.write_text('complete')
            cache = {'signature':'input-v1', 'outputs':{'generated.html':renderer.file_digest(output)}}
            (root / '.lake/textbook-build.json').write_text(json.dumps(cache))
            with patch.object(renderer, 'ROOT', root), \
                    patch.object(renderer, 'OUT', root / 'docs'), \
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
