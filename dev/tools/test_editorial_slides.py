"""Authored boundaries and cumulative reveals must preserve the source."""
import re
import unittest

import editorial_slides as editorial
import slides


class EditorialSlidesTest(unittest.TestCase):
    def pages(self, body, pages=None, splits=None, include_notes=False):
        return editorial.paginate(slides.blocks_from_html(body, 'T'), {
            'version': 2,
            'pages': pages or [{'at': {'tag': 'h2'}, 'id': 'topic', 'label': '話題'}],
            'splits': splits or [],
        }, 'T', include_notes=include_notes)

    def nodes(self, html):
        return [n for n in slides.FragmentParser(html).root.children if isinstance(n, slides.Node)]

    def visible_text(self, node):
        if isinstance(node, str):
            return node
        if 'data-unrevealed' in node.attrs:
            return ''
        return ''.join(self.visible_text(child) for child in node.children)

    def test_semantic_page_anchor_survives_insertions(self):
        body = '<h2>導入</h2><p>説明。</p><pre class="lean">#check Nat</pre><p>結論。</p>'
        pages = [{'at': {'tag': 'h2'}, 'id': 'intro', 'label': '導入'},
                 {'at': {'code': '#check Nat'}, 'id': 'nat', 'label': 'Nat の型'}]
        for source in [body, body.replace('<p>説明。</p>', '<p>追加。</p><p>別の説明。</p>')]:
            actual = self.pages(source, pages)
            self.assertEqual([p.id for p in actual], ['t-intro', 't-nat'])
            self.assertEqual(actual[1].steps[0][0].node.text, '#check Nat')

    def test_prose_reveals_share_one_paragraph_and_retain_inline_markup(self):
        body = '<h2>項と型</h2><p>すべての項は型を持つ。型の表記も<code>項</code>である。</p>'
        pages = self.pages(body, splits=[{'at': {'tag': 'p'}, 'before': ['型の表記も']}])
        content = editorial.render_content(pages[0])
        self.assertEqual(content.count('<p>'), 1)
        self.assertEqual(len(pages[0].steps), 2)
        self.assertIn('<code>項</code>', content)
        printed = self.nodes(slides.slide_articles(pages, print_steps=True, chapter='T'))
        self.assertNotIn('型の表記も', self.visible_text(printed[0]))
        self.assertIn('型の表記も項である。', self.visible_text(printed[1]))

    def test_pdf_reserves_identical_content_geometry_at_every_stage(self):
        page = self.pages('<h2>例</h2><p>説明。</p><pre class="lean">#check Nat</pre>'
                          '<pre class="quote">Nat : Type</pre>')[0]
        stages = [editorial.render_content(page, stage, reserve_space=True)
                  for stage in range(1, len(page.steps) + 1)]
        self.assertEqual(len(set(re.sub(r' data-unrevealed="" aria-hidden="true"', '', s) for s in stages)), 1)
        first = slides.FragmentParser(stages[0]).root
        self.assertNotIn('#check Nat', self.visible_text(first))
        self.assertIn('#check Nat', first.text)

    def test_columns_use_a_semantic_block_boundary_and_keep_stage_order(self):
        body = '<h2>比較</h2><p>正常例。</p><pre class="lean">#check 3</pre><p>エラー例。</p><pre class="quote">error</pre>'
        defs = [{'at': {'tag': 'h2'}, 'id': 'compare', 'label': '比較',
                 'column_at': {'tag': 'p', 'starts': 'エラー例。'}}]
        page = self.pages(body, defs)[0]
        rendered = editorial.render_content(page)
        self.assertEqual(rendered.count('class="slide-column"'), 2)
        columns = self.nodes(rendered)[0].children
        columns = [c for c in columns if isinstance(c, slides.Node)]
        self.assertIn('#check 3', columns[0].text)
        self.assertNotIn('エラー例', columns[0].text)
        self.assertIn('エラー例', columns[1].text)
        self.assertIn('data-step="2"', columns[1].render())
        for bad in [{'tag': 'h2'}, {'tag': 'p', 'starts': '存在しない'}]:
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                self.pages(body, [dict(defs[0], column_at=bad)])

    def test_code_reveals_keep_one_code_box_and_exact_whitespace(self):
        code = '<span class="kw">def</span> f :=\n  fun x =&gt; x\n\n#check f'
        pages = self.pages('<h2>定義</h2><pre class="lean"><code>' + code + '</code></pre>',
                           splits=[{'at': {'tag': 'pre'}, 'before': ['  fun x', '#check f']}])
        result = editorial.render_content(pages[0])
        self.assertEqual(result.count('<pre'), 1)
        self.assertEqual(result.count('<code>'), 1)
        self.assertIn('<span class="kw">def</span>', result)
        pre = self.nodes(result)[1]
        self.assertEqual(pre.text, 'def f :=\n  fun x => x\n\n#check f')
        self.assertNotIn('#check f', editorial.render_content(pages[0], 2))

    def test_table_is_revealed_as_one_block(self):
        body = '<h2>対応表</h2><table><thead><tr><th>型</th><th>命題</th></tr></thead>' \
               '<tbody><tr><td>積</td><td>かつ</td></tr><tr><td>和</td><td>または</td></tr></tbody></table>'
        page = self.pages(body)[0]
        self.assertEqual(len(page.steps), 1)
        rendered = editorial.render_content(page)
        self.assertEqual(rendered.count('<table>'), 1)
        self.assertEqual(rendered.count('<thead'), 1)
        self.assertNotIn('data-step="1"', rendered)
        self.assertIn('または', editorial.render_content(page, 1))

    def test_list_is_revealed_as_one_block_with_its_numbering(self):
        body = '<h2>推論</h2><ol start="3"><li>第3段。</li><li>第4段。</li></ol>'
        page = self.pages(body)[0]
        self.assertEqual(len(page.steps), 1)
        result = editorial.render_content(page)
        self.assertEqual(result.count('<ol'), 1)
        self.assertIn('start="3"', result)
        self.assertIn('第4段', editorial.render_content(page, 1))

    def test_default_reveals_whole_paragraphs_and_whole_code_blocks(self):
        body = '<h2>項と型</h2><p>最初の文。次の文。</p>' \
               '<pre class="lean">def f :=\n  fun x =&gt; x\n\n#check f</pre>' \
               '<pre class="quote">f : Nat → Nat</pre><p>型の説明。続く説明。</p>'
        page = self.pages(body)[0]
        self.assertEqual(len(page.steps), 4)
        self.assertIn('最初の文。次の文。', editorial.render_content(page, 1))
        self.assertNotIn('def f', editorial.render_content(page, 1))
        self.assertIn('#check f', editorial.render_content(page, 2))
        self.assertNotIn('f : Nat', editorial.render_content(page, 2))
        self.assertIn('型の説明。続く説明。', editorial.render_content(page, 4))

    def test_question_sentences_share_one_number_and_answer_follows(self):
        body = '<h2>✏ 練習</h2><ol start="42" data-exercise="42"><li>型を予想せよ。値も求めよ。</li></ol>' \
               '<pre class="quote">#check f</pre><p>を試すこと。</p>' \
               '<details class="sol"><summary>解答 42</summary><p>答え。</p></details>'
        page = self.pages(body, splits=[{'at': {'tag': 'ol'}, 'before': ['値も求めよ。']}])[0]
        result = editorial.render_content(page)
        self.assertEqual(result.count('<li>'), 1)
        self.assertIn('start="42"', result)
        self.assertEqual(''.join(b.node.text for b in page.steps[-1]), '解答 42答え。')
        items = editorial.source_items(slides.blocks_from_html(body, 'T'))
        self.assertEqual(items[-1].question, '型を予想せよ。値も求めよ。')
        self.assertNotIn('解答', editorial.render_content(page, len(page.steps) - 1))

    def test_page_can_start_at_an_authored_part_inside_code(self):
        body = '<h2>関数</h2><pre class="lean">def first := 1\n\ndef second := 2</pre>'
        page_defs = [{'at': {'tag': 'h2'}, 'id': 'first', 'label': '最初の関数'},
                     {'at': {'tag': 'pre', 'part': 'def second'}, 'id': 'second', 'label': '次の関数'}]
        pages = self.pages(body, page_defs, [{'at': {'tag': 'pre'}, 'before': ['def second']}])
        self.assertNotIn('def second', editorial.render_content(pages[0]))
        self.assertIn('def second := 2', editorial.render_content(pages[1]))

    def test_notes_interrupt_and_resume_in_source_order_only_when_enabled(self):
        body = '<h2>導入</h2><p>前。</p><aside class="note note--optional"><h3>補足</h3><p>注。</p></aside><p>後。</p>'
        default = self.pages(body)
        self.assertEqual(len(default), 1)
        self.assertNotIn('注。', editorial.render_content(default[0]))
        with_notes = self.pages(body, include_notes=True)
        content = ''.join(b.source_text for p in with_notes for stage in p.steps for b in stage)
        self.assertEqual(content, '導入前。補足注。後。')
        self.assertEqual(len(with_notes), len({p.id for p in with_notes}))

    def test_no_automatic_page_break_or_import_only_stage(self):
        body = '<pre class="lean">import A\nimport B</pre><h2>導入</h2><p>' + '文章。' * 500 + '</p>'
        pages = self.pages(body, [{'at': {'tag': 'pre'}, 'id': 'intro', 'label': '導入'}])
        self.assertEqual(len(pages), 1)
        self.assertEqual(len(pages[0].steps), 1)
        self.assertIn('導入', ''.join(b.node.text for b in pages[0].steps[0]))

    def test_invalid_or_stale_anchors_fail_loudly(self):
        for before in [['存在しない'], ['次。', '次。'], ['前。']]:
            with self.subTest(before=before), self.assertRaises(ValueError):
                self.pages('<h2>見出し</h2><p>前。次。</p>', splits=[{'at': {'tag': 'p'}, 'before': before}])
        with self.assertRaises(ValueError):
            self.pages('<h2>見出し</h2><p>前。</p><p>後。</p>',
                       [{'at': {'tag': 'p'}, 'id': 'ambiguous', 'label': '重複'}])


if __name__ == '__main__':
    unittest.main()
