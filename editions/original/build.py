#!/usr/bin/env python3
"""旧版（1往復構成）の HTML を、リポジトリ共通の生成スクリプトで作る。

本文は editions/original/src、出力は公開ページの docs/original/。
正本（2往復構成）の src/・docs/ には書き込まない。
"""

import argparse
from pathlib import Path
import sys

EDITION = Path(__file__).resolve().parent
REPOSITORY = EDITION.parent.parent
sys.path.insert(0, str(REPOSITORY / "tools"))
import lean2html as renderer  # noqa: E402
import refs  # noqa: E402


def configure():
    renderer.ROOT = EDITION
    renderer.SRC = EDITION / "src"
    renderer.OUT = REPOSITORY / "docs" / "original"
    renderer.PDF_OUT = EDITION / "pdf" / "all.pdf"
    renderer.CHAPTERS = ["Intro1", "CH", "Intro2", "Top", "Extra"]
    renderer.SOL_FILES = {name: name + "Sol" for name in renderer.CHAPTERS if name != "Extra"}
    refs.SECTION_STARTS = {"CH": 0}
    renderer.SITE_TITLE = "はじめての Lean — 旧版（1往復構成）"
    renderer.SITE_CONCEPT = (
        "これは2往復構成に改める前の旧版で、比較・参照のために残している。"
        "最新版は<a href=\"../index.html\">こちら</a>。"
    )
    renderer.SITE_GOALS = (
        "<h2>構成と読む順</h2>"
        "<p>読む順は Intro1 → CH → Intro2 → Top（→ 演習 Extra）。"
        "Intro1 で型と項の読み方を一通り学んでから、CH で証明の読み方に進む。</p>"
    )
    renderer.SITE_NOTE = "各 ✏ 練習には折りたたみの解答が付いている。"
    renderer.ROLES = {
        "Intro1": "コードの読み方の基礎（項と型、関数、帰納型、structure、依存関数）",
        "CH": "証明が検査される仕組み",
        "Intro2": "位相空間を読むための道具",
        "Top": "コンパクト空間からハウスドルフ空間への連続全単射",
        "Extra": "演習（sorry を自分で埋める）",
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--no-pdf", action="store_true", help="HTML だけを生成する")
    configure()
    renderer.main(with_pdf=not ap.parse_args().no_pdf)


if __name__ == "__main__":
    main()
