"""The introductory chapters must run without importing or bundling other chapters."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import bundle


class BundleTest(unittest.TestCase):
    def test_introductory_chapters_are_standalone(self):
        for name in sorted(bundle.STANDALONE_CHAPTERS):
            with self.subTest(chapter=name):
                source = bundle.ROOT / 'src' / f'{name}.lean'
                self.assertNotRegex(bundle.strip_comments(source.read_text()), r'(?m)^import\s')
                self.assertEqual(bundle.dependency_order('Original', name), [])
                result = bundle.bundle(name)
                self.assertNotRegex(bundle.strip_comments(result), r'(?m)^import\s')
                self.assertNotIn('前の章のコード', result)
                self.assertIn('\n'.join(bundle.body(bundle.module_path('Original', name))).strip(), result)

    def test_new_import_in_standalone_chapter_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(bundle, 'LESSONS', Path(tmp)):
            original = Path(tmp) / 'Original'
            original.mkdir()
            (original / '02_Forall.lean').write_text('import LeanIntro.Original.«01_TypesAndTerms»\n')
            with self.assertRaisesRegex(ValueError, '単独実行'):
                bundle.bundle('02_Forall')

    def test_later_chapters_still_include_only_their_dependencies(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(bundle, 'LESSONS', Path(tmp)):
            original = Path(tmp) / 'Original'
            original.mkdir()
            (original / 'A.lean').write_text('def a : Nat := 1\n#check a\n')
            (original / 'Unused.lean').write_text('def unused : Nat := 2\n')
            (original / 'B.lean').write_text('import LeanIntro.Original.«A»\n#check a\n')
            result = bundle.bundle('B')
            self.assertIn('def a : Nat := 1', result)
            self.assertNotIn('unused', result)
            self.assertEqual(result.count('#check a'), 1)
            self.assertNotRegex(result, r'(?m)^import\s')


if __name__ == '__main__':
    unittest.main()
