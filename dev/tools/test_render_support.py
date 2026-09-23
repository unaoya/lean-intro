"""Regression checks for the comment examples in the textbook."""

from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from render_support import parse


class CommentExamplesTest(unittest.TestCase):
    def parse_text(self, text):
        with TemporaryDirectory() as directory:
            path = Path(directory) / "Example.lean"
            path.write_text(text, encoding="utf-8")
            return parse(path, with_line_numbers=True)

    def test_nested_examples_remain_prose(self):
        result = self.parse_text(
            "/-! コメントの例\n    /- 外側 /- 内側 -/ 続き -/\n"
            "説明はここまで。\n-/\n\ndef x : Nat := 2\n"
        )
        self.assertEqual(result[0], ("prose", 1, [
            "コメントの例", "    /- 外側 /- 内側 -/ 続き -/", "説明はここまで。", ""
        ]))
        self.assertEqual(result[1], ("code", 6, ["def x : Nat := 2"]))

    def test_field_docstrings_remain_code(self):
        result = self.parse_text(
            "/-- 点。 -/\nstructure Point where\n  /-- 座標。 -/\n  x : Nat\n"
        )
        self.assertEqual(result[0], ("doc", 1, ["点。"]))
        self.assertEqual(result[1][0:2], ("code", 2))
        self.assertIn("  /-- 座標。 -/", result[1][2])

    def test_unclosed_comment_fails(self):
        with self.assertRaisesRegex(ValueError, "unclosed prose comment"):
            self.parse_text("/-! 閉じていない\n/- 入れ子 -/\n")


if __name__ == "__main__":
    unittest.main()
