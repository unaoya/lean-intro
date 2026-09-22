"""Behavior tests: renumbering, failure atomicity, rendering, and solution routing."""

import contextlib
import io
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import lean2html as html
import refs


class RefTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.src = self.root / 'src'
        self.src.mkdir()
        self.chapters = ['Intro1', 'CH']
        self.sol_files = {}
        self.put('Intro1', '/-! ## 1. 最初 {#sec-first}\n-/\n/-! ## 2. 次 {#sec-second}\n-/\n')
        self.put('CH', '/-! ## 0. 証明 {#sec-proof}\n-/\n')

    def put(self, name, text):
        (self.src / f'{name}.lean').write_text(text, encoding='utf-8')

    def read(self, name):
        return (self.src / f'{name}.lean').read_text(encoding='utf-8')

    def analyze(self):
        return refs.analyze(self.src, self.chapters, self.sol_files, html.parse)

    def test_insert_and_reorder_updates_numbers_not_identity(self):
        self.put('Intro1', '/-! ## 2. 次 {#sec-second}\n-/\n'
                 '/-! ## 挿入 {#sec-new}\n-/\n'
                 '/-! ## 1. 最初 {#sec-first}\n'
                 'これが[1節](#sec-first)。[節](#sec-new)も参照。\n-/\n')
        self.put('CH', '/-! ## 0. 証明 {#sec-proof}\n'
                 '[`Intro1.lean`\n   2節](#sec-second)と[1 節](#sec-first)。\n-/\n')
        self.sol_files = {'Intro1': 'Intro1Sol'}
        self.put('Intro1Sol', '/-! SOL first:1 -/\n/-- 本文 [1節](#sec-first) -/\n')
        result = self.analyze()
        self.assertEqual(result.errors, [])
        result.write()
        self.assertIn('## 3. 最初', self.read('Intro1'))
        self.assertIn('これが[3節](#sec-first)', self.read('Intro1'))
        self.assertIn('[2節](#sec-new)', self.read('Intro1'))
        self.assertIn('[`Intro1.lean`\n   1節](#sec-second)', self.read('CH'))
        self.assertIn('[`Intro1.lean` 3 節](#sec-first)', self.read('CH'))
        self.assertIn('本文 [3節](#sec-first)', self.read('Intro1Sol'))
        self.assertEqual(self.analyze().changes, [])
        self.assertEqual(self.analyze().write(), [])

    def test_cross_chapter_move_and_ranges(self):
        self.put('Intro1', '/-! ## 次 {#sec-second}\n'
                 '[1](#sec-first)〜[2節](#sec-second)\n-/\n')
        self.put('CH', '/-! ## 最初 {#sec-first}\n'
                 '[`Intro1.lean` の1節](#sec-first)\n-/\n')
        result = self.analyze()
        self.assertEqual(result.errors, [])
        result.write()
        self.assertIn('[`CH.lean` 0](#sec-first)〜[1節](#sec-second)', self.read('Intro1'))
        self.assertIn('[`CH.lean` の0節](#sec-first)', self.read('CH'))

    def test_unknown_and_duplicate_labels_prevent_all_writes(self):
        self.put('Intro1', '/-! ## 99. 最初 {#sec-first}\n[節](#sec-missing)\n-/\n')
        self.put('CH', '/-! ## 0. 重複 {#sec-first}\n-/\n')
        original = self.read('Intro1')
        result = self.analyze()
        self.assertTrue(any('Intro1.lean:2:' in e and '存在しません' in e for e in result.errors))
        self.assertTrue(any('CH.lean:1:' in e and '重複' in e for e in result.errors))
        with self.assertRaises(ValueError):
            result.write()
        self.assertEqual(self.read('Intro1'), original)

    def test_unmarked_japanese_space_and_range_are_detected(self):
        self.put('Intro1', '/-! ## 1. 最初 {#sec-first}\n'
                 'これが7節、後の 11 節、2〜4節。\n'
                 '`CH.lean`（4節）\n-/\n')
        result = self.analyze()
        self.assertEqual(len(result.errors), 5)
        self.assertTrue(all('固定ラベルのない' in e for e in result.errors))

    def test_suppression_does_not_hide_explicit_bad_labels(self):
        self.put('Intro1', '/-! ## 1. 最初 {#sec-first}\n'
                 '-- refcheck: ignore-next-line\nこれが99節。\n'
                 '88 節 refcheck-ignore\n'
                 '[節](#sec-missing) refcheck-ignore\n-/\n')
        result = self.analyze()
        self.assertEqual(len(result.errors), 1)
        self.assertIn('Intro1.lean:5:', result.errors[0])
        self.assertIn('存在しません', result.errors[0])

    def test_heading_scope_line_numbers_keywords_and_supplements(self):
        self.put('Intro1', '-- ## 8. code {#sec-fake}\n\n'
                 '/-- ## 9. doc {#sec-doc} -/\n'
                 '/-! ## 1. `最初` {#sec-first}\n'
                 '### 補足（任意）: 詳細\n'
                 '[1節](#sec-first)（最初）、[1節](#sec-first)の補足\n'
                 '## 無番号\n### 補足: ここは別\n-/\n')
        result = self.analyze()
        self.assertEqual(result.errors, [])
        self.assertEqual(set(result.sections), {'first', 'proof'})
        self.assertEqual(result.sections['first'].line, 4)
        self.assertEqual(len(result.sections['first'].supplements), 1)
        self.put('CH', '/-! ## 0. 証明 {#sec-proof}\n'
                 '[節](#sec-first)（別題）、[0節](#sec-proof)の補足\n-/\n')
        result = self.analyze()
        self.assertEqual(len(result.errors), 2)

    def test_malformed_and_unlabelled_headings_fail(self):
        self.put('Intro1', '/-! ## 1. 無ラベル\n'
                 '[節](#sec-bad label)\n[自由文](#sec-proof)\n-/\n')
        result = self.analyze()
        self.assertEqual(len(result.errors), 3)

    def test_heading_and_nested_reference_updates_do_not_overlap(self):
        self.put('Intro1', '/-! ## 99. [99節](#sec-second)の復習 {#sec-first}\n-/\n'
                 '/-! ## 新規 {#sec-second}\n-/\n')
        result = self.analyze()
        self.assertEqual(result.errors, [])
        result.write()
        self.assertIn('## 1. [2節](#sec-second)の復習 {#sec-first}', self.read('Intro1'))
        self.assertEqual(self.analyze().changes, [])

    def test_documentation_headings_do_not_create_section_targets(self):
        self.put('Intro1', '/-! ## 1. 最初 {#sec-first}\n-/\n'
                 '/-- ## 1. 最初 {#sec-first} -/\n')
        with patch.object(html, 'SOL_FILES', {}):
            body = html.render_chapter('Intro1', html.parse(self.src/'Intro1.lean'), self.analyze().sections)
        self.assertEqual(body.count('id="sec-first"'), 1)

    def test_concurrent_edits_are_not_overwritten(self):
        self.put('Intro1', '/-! ## 最初 {#sec-first}\n-/\n')
        result = self.analyze()
        self.put('CH', 'user edit\n')
        with self.assertRaisesRegex(ValueError, '検査後に変更'):
            result.write()
        self.assertNotIn('## 1.', self.read('Intro1'))

    def test_prose_links_and_code_display(self):
        result = self.analyze()
        prose = html.render_prose([
            '## 1. 最初 {#sec-first}',
            '**[1節](#sec-first)**、[`CH.lean` 0節](#sec-proof)。',
            '', '* [2節](#sec-second)', '',
            '| 節 |', '| --- |', '| [1節](#sec-first) |', '',
            '    [1節](#sec-first)',
        ], 'Intro1', result.sections)
        self.assertIn('<h2 id="sec-first">1. 最初</h2>', prose)
        self.assertIn('<strong><a href="#sec-first">1節</a></strong>', prose)
        self.assertIn('<a href="ch.html#sec-proof"><code>CH.lean</code> 0節</a>', prose)
        self.assertIn('<li><a href="#sec-second">2節</a></li>', prose)
        self.assertIn('<pre class="quote"><code>1節</code></pre>', prose)
        self.assertNotIn('{#sec-', prose)
        code = html.render_code(['-- [1節](#sec-first)', 'def x := 1'])
        self.assertEqual(code, html.render_code(['-- 1節', 'def x := 1']))
        self.assertEqual(html.inline('``a ` b`` **`x`**'), '<code>a ` b</code> <strong><code>x</code></strong>')

    def test_line_join_uses_visible_text_including_wrapped_links(self):
        for parts in [
            ['これは、', '[1節](#sec-first)で見る。'],
            ['参照は、', '[`CH.lean`', '0節](#sec-proof)です。'],
            ['範囲は[1](#sec-first)', 'から。'],
        ]:
            original = refs.stripped('\n'.join(parts)).split('\n')
            self.assertEqual(refs.stripped(html.smart_join(parts)), html.smart_join(original))

    def test_solutions_follow_section_identity_with_repeated_items(self):
        self.sol_files = {'Intro1': 'Intro1Sol'}
        self.put('Intro1', '/-! ## 2. 次 {#sec-second}\n-/\n'
                 '/-! ### ✏ 練習\n1. 次の問題\n-/\n'
                 '/-! ## 1. 最初 {#sec-first}\n-/\n'
                 '/-! ### ✏ 練習\n1. 最初の問題\n-/\n'
                 '/-! ### ✏ 練習\n1. 同節の別問題\n-/\n')
        self.put('Intro1Sol', '/-! SOL first:1 -/\n/-- FIRST [節](#sec-first) -/\n'
                 '/-! SOL first:1 -/\n/-- REPEATED -/\n'
                 '/-! SOL second:1 -/\n/-- SECOND -/\n')
        result = self.analyze()
        self.assertEqual(result.errors, [])
        result.write()
        with patch.object(html, 'SRC', self.src), patch.object(html, 'SOL_FILES', self.sol_files):
            body = html.render_chapter('Intro1', html.parse(self.src/'Intro1.lean'), result.sections)
            self.assertLess(body.index('SECOND'), body.index('FIRST'))
            self.assertLess(body.index('FIRST'), body.index('REPEATED'))
            self.assertIn('FIRST <a href="#sec-first">2節</a>', body)
            self.put('Intro1Sol', self.read('Intro1Sol').replace('SOL second:1', 'SOL second:2'))
            with self.assertRaisesRegex(SystemExit, '順序を確認'):
                html.render_chapter('Intro1', html.parse(self.src/'Intro1.lean'), result.sections)

    def test_missing_extra_and_invalid_solutions(self):
        self.sol_files = {'Intro1': 'Intro1Sol'}
        self.put('Intro1', '/-! ## 1. 最初 {#sec-first}\n-/\n/-! ### ✏ 練習\n1. 問題\n-/\n')
        with patch.object(html, 'SRC', self.src), patch.object(html, 'SOL_FILES', self.sol_files):
            self.put('Intro1Sol', '')
            with self.assertRaisesRegex(SystemExit, '解答がない'):
                html.render_chapter('Intro1', html.parse(self.src/'Intro1.lean'))
            self.put('Intro1Sol', '/-! SOL first:1 -/\n/-- A -/\n/-! SOL first:2 -/\n/-- B -/\n')
            with self.assertRaisesRegex(SystemExit, '余っている'):
                html.render_chapter('Intro1', html.parse(self.src/'Intro1.lean'))
        self.put('Intro1Sol', '/-! SOL 1.1 -/\n/-! SOL proof:1 -/\n')
        self.assertEqual(len(self.analyze().errors), 2)

    def test_html_generation_syncs_and_fails_before_output(self):
        out = self.root/'docs'
        with patch.object(html, 'SRC', self.src), patch.object(html, 'OUT', out), \
             patch.object(html, 'CHAPTERS', self.chapters), patch.object(html, 'SOL_FILES', {}), \
             contextlib.redirect_stdout(io.StringIO()):
            self.put('Intro1', '/-! ## 最初 {#sec-first}\n[節](#sec-first)\n-/\n')
            html.main(with_pdf=False)
            before = (out/'intro1.html').read_bytes()
            self.assertIn('[1節]', self.read('Intro1'))
            self.put('Intro1', self.read('Intro1').replace('](#sec-first)', '](#sec-unknown)'))
            with self.assertRaisesRegex(SystemExit, 'Intro1.lean:2:'):
                html.main(with_pdf=False)
            self.assertEqual((out/'intro1.html').read_bytes(), before)

    def test_cli_check_is_read_only_fix_is_idempotent(self):
        dest = self.root/'tools'
        dest.mkdir()
        for name in ['lean2html.py', 'refs.py', 'check_refs.py']:
            shutil.copy(Path(__file__).parent/name, dest/name)
        for name in ['Intro2', 'Top', 'Extra', 'Intro1Sol', 'CHSol', 'Intro2Sol', 'TopSol']:
            self.put(name, '')
        self.put('Intro1', '/-! ## 最初 {#sec-first}\n[節](#sec-first)\n-/\n')
        original = self.read('Intro1')
        command = [sys.executable, '-B', str(dest/'check_refs.py')]
        run = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(run.returncode, 1)
        self.assertIn('Intro1.lean:1:', run.stderr)
        self.assertEqual(self.read('Intro1'), original)
        run = subprocess.run(command+['--fix'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        run = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.put('Intro1', self.read('Intro1').replace('](#sec-first)', '](#sec-missing)'))
        broken = self.read('Intro1')
        run = subprocess.run(command+['--fix'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 1)
        self.assertEqual(self.read('Intro1'), broken)
        run = subprocess.run([sys.executable, '-B', str(dest/'lean2html.py'), '--no-pdf'], capture_output=True, text=True)
        self.assertNotEqual(run.returncode, 0)
        self.assertIn('Intro1.lean:2:', run.stderr)
        self.assertFalse((self.root/'docs').exists())

    def test_combined_document_links_are_local_and_unique(self):
        sections = self.analyze().sections
        titles = {'Intro1': '第一章', 'CH': '証明'}
        bodies = {name: html.render_prose([
            f'## {section.number}. {section.title} {{#sec-{section.label}}}',
            '[`CH.lean` 0節](#sec-proof)'], name, sections)
            for name, section in [('Intro1', sections['first']), ('CH', sections['proof'])]}
        with patch.object(html, 'CHAPTERS', self.chapters):
            combined = html.pdf_html(titles, bodies)
        self.assertNotIn('href="ch.html#', combined)
        self.assertEqual(combined.count('id="sec-proof"'), 1)
        self.assertIn('href="#sec-proof"', combined)


if __name__ == '__main__':
    unittest.main()
