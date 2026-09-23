#!/usr/bin/env python3
"""本文の src/*.lean から、受講者用の Lean ファイル（解説を省いた版）を作る。

出力は独立した Lake プロジェクト student/ の student/src/*.lean。
説明は HTML で読み、手元ではコードを動かす、という使い方を想定する。

残すもの:
  * すべてのコード（補足の枠の中のコードも含む。後のコードが前の定義を使うため）
  * 節見出し（`-- ## …`・`-- ### …`）
  * コード行の中の `--` コメント
  * ✏ 練習の問題文（`/- … -/` のコメントとして。数式の記法は Unicode に戻す）
  * 地の文の中で示した Lean のコード例（エラーの例など）。`-- ` でコメントアウトする

消すもの:
  * 地の文・docstring
  * `#check`・`#eval` などの直後に置いた出力の表示ブロック（受講者は自分で確かめる）
  * 補足・先取りの枠の印（CALLOUT_START/END）

使い方:
    python3 tools/student.py          # student/src/*.lean を生成
    lake -d student build             # 生成したファイルがコンパイルできるか検査
"""

from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from render_support import parse  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"
OUT = ROOT / "student" / "src"

HEADING_RE = re.compile(r"^(#{1,3}) (.*)$")
LABEL_RE = re.compile(r"\s*\{#sec-[^}]*\}\s*$")
REF_RE = re.compile(r"\[((?:[^\[\]]|`[^`]*`)+)\]\(#sec-[^)]*\)")
LEAN_START_RE = re.compile(
    r"^(def|theorem|example|instance|inductive|structure|class|abbrev|axiom|open|namespace|"
    r"end|variable|#check|#eval|#print|#reduce|macro_rules|syntax|notation|infixl|infixr|"
    r"@\[|noncomputable|/-|--)\b|^(#check|#eval|#print|#reduce)")
OUTPUT_START_RE = re.compile(r"^(error|warning|info)\b|^Hint:")

# 数式（KaTeX 記法）を、受講者用ファイルで読みやすい Unicode に戻す
TEX = {
    r"\to": "→", r"\mapsto": "↦", r"\times": "×", r"\circ": "∘", r"\forall": "∀",
    r"\exists": "∃", r"\cong": "≅", r"\subseteq": "⊆", r"\subset": "⊂", r"\in": "∈",
    r"\notin": "∉", r"\sqcup": "⊔", r"\prod": "∏", r"\sum": "∑", r"\le": "≤", r"\leq": "≤",
    r"\ge": "≥", r"\geq": "≥", r"\neq": "≠", r"\ne": "≠", r"\cdot": "·", r"\lambda": "λ",
    r"\infty": "∞", r"\neg": "¬", r"\land": "∧", r"\lor": "∨", r"\cap": "∩", r"\cup": "∪",
    r"\emptyset": "∅", r"\alpha": "α", r"\beta": "β", r"\gamma": "γ", r"\sigma": "σ",
    r"\bigl": "", r"\bigr": "", r"\Bigl": "", r"\Bigr": "", r"\left": "", r"\right": "",
    r"\quad": "  ", r"\ldots": "…", r"\dots": "…", r"\{": "{", r"\}": "}", r"\,": " ", r"\;": " ",
}
BB = {"N": "ℕ", "Z": "ℤ", "Q": "ℚ", "R": "ℝ", "C": "ℂ"}


def tex_to_unicode(expr: str) -> str:
    expr = re.sub(r"\\mathbb\{(\w)\}", lambda m: BB.get(m[1], m[1]), expr)
    expr = re.sub(r"\\(?:mathrm|operatorname|text|mathit)\{([^{}]*)\}", r"\1", expr)
    for key in sorted(TEX, key=len, reverse=True):
        expr = re.sub(re.escape(key) + r"(?![A-Za-z])", TEX[key], expr)
    expr = re.sub(r"_\{([^{}]*)\}", r"_\1", expr)
    expr = re.sub(r"\^\{([^{}]*)\}", r"^\1", expr)
    return re.sub(r"  +", " ", expr).strip()


def plain(text: str) -> str:
    """問題文を受講者用ファイル向けに整える: 数式を Unicode に、節参照を表示文字列に。"""
    text = re.sub(r"\$\$(.+?)\$\$", lambda m: tex_to_unicode(m[1]), text)
    text = re.sub(r"\$(.+?)\$", lambda m: tex_to_unicode(m[1]), text)
    return REF_RE.sub(r"\1", text)


def indented_blocks(lines):
    """地の文の中の字下げブロック（4字下げ）を、(開始位置, 行のリスト) で順に返す。"""
    i, n = 0, len(lines)
    while i < n:
        if lines[i].startswith("    "):
            block = []
            while i < n:
                if lines[i].startswith("    "):
                    block.append(lines[i][4:])
                    i += 1
                elif not lines[i].strip() and i + 1 < n and lines[i + 1].startswith("    "):
                    block.append("")
                    i += 1
                else:
                    break
            yield block
        else:
            i += 1


def lean_examples(lines, skip_first: bool):
    """地の文の中の Lean のコード例を、コメントアウトした行のリストで返す。
    skip_first=True なら最初の字下げブロックは直前のコマンドの出力なので飛ばす。"""
    out = []
    for k, block in enumerate(indented_blocks(lines)):
        if skip_first and k == 0:
            continue
        rows = []
        for row in block:
            if OUTPUT_START_RE.match(row.strip()):
                break          # 以降はエラーなどの出力の引用
            rows.append(row)
        while rows and not rows[-1].strip():
            rows.pop()
        if rows and LEAN_START_RE.match(rows[0].strip()):
            out.append("-- 本文の例（コメントアウトしてある。名前が重なるものもある）:")
            out.extend("-- " + r if r.strip() else "--" for r in rows)
            out.append("")
    return out


def prose_to_student(lines, after_command: bool, in_callout: bool = False):
    """地の文1ブロックから、見出し・練習の問題文・コード例だけを取り出す。"""
    out = []
    body = [l for l in lines if l.strip() not in ("CALLOUT_START optional", "CALLOUT_START preview",
                                                    "CALLOUT_END")]
    heading = None
    for idx, line in enumerate(body):
        m = HEADING_RE.match(line)
        if m:
            heading = (idx, len(m[1]), LABEL_RE.sub("", m[2]))
            break
    if heading and "✏ 練習" in heading[2]:
        text = "\n".join(body[heading[0] + 1:]).strip("\n")
        return ["/- " + heading[2], plain(text), "-/", ""]
    if heading:
        idx, level, title = heading
        if re.match(r"(補足|先取り)", title) and not in_callout:
            # 地の文だけの補足・先取りの枠。コードを含まないので見出しも出さない
            return lean_examples(body, skip_first=after_command)
        out += [""] if level > 1 else []
        out.append(f"-- {'#' * level} {plain(title)}")
        out.append("")
    out += lean_examples(body, skip_first=after_command)
    return out


def student_file(path: Path) -> str:
    out = []
    after_command = False
    in_callout = False
    for kind, lines in parse(path):
        if kind == "code":
            out.extend(lines)
            out.append("")
            # コード片の最後の文（字下げしていない行から始まる）が #check などなら、
            # 直後の地の文の最初の字下げブロックはその出力である
            tops = [l for l in lines if l.strip() and not l.startswith((" ", "\t"))]
            after_command = bool(tops) and bool(re.match(r"#(check|eval|print|reduce)\b", tops[-1]))
        elif kind == "prose":
            marker = [l.strip() for l in lines if l.strip()]
            if marker and marker[0].startswith("CALLOUT_START"):
                in_callout = True
                continue
            if marker == ["CALLOUT_END"]:
                in_callout = False
                out += ["-- （補足・先取りここまで）", ""]
                continue
            out.extend(prose_to_student(lines, after_command, in_callout))
            after_command = False
        # docstring は捨てる
    # 中身（コード・練習・例）が1つもない小見出しは出さない
    END = "-- （補足・先取りここまで）"
    kept, skip_end = [], False
    for i, line in enumerate(out):
        if line == END and skip_end:
            skip_end = False
            continue
        if line.startswith("-- ### "):
            rest = next((l for l in out[i + 1:] if l.strip()), "")
            if rest.startswith("-- #"):
                continue
            if rest == END:           # 中身のない枠は、見出しも終わりの印も出さない
                skip_end = True
                continue
        kept.append(line)
    text = "\n".join(kept)
    return re.sub(r"\n{3,}", "\n\n", text).strip() + "\n"


def main(docs: Path | None = None, titles: dict | None = None):
    sys.path.insert(0, str(ROOT / "tools"))
    import lean2html
    OUT.mkdir(parents=True, exist_ok=True)
    header = ("-- 受講者用ファイル（解説は HTML 版で読む）。tools/student.py が src/ から自動生成する。\n"
              "-- 手で編集しないこと。\n\n")
    for name in lean2html.CHAPTERS:
        text = student_file(SRC / f"{name}.lean")
        (OUT / f"{name}.lean").write_text(header + text, encoding="utf-8")
        print(f"  student/src/{name}.lean")
    for stale in OUT.glob("*.lean"):
        if stale.stem not in lean2html.CHAPTERS:
            stale.unlink()
    if docs is not None:
        publish(docs, lean2html.CHAPTERS, titles or {})
    roots = ", ".join("`«" + name + "»" for name in lean2html.CHAPTERS)
    (OUT.parent / "lakefile.lean").write_text(f"""import Lake
open Lake DSL

-- 受講者用ファイル（tools/student.py が src/ から自動生成）。解答は含まない。
package «lean_intro_student» where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

@[default_target]
lean_lib «LeanIntroStudent» where
  srcDir := "src"
  roots := #[{roots}]
""", encoding="utf-8")


def publish(docs: Path, chapters, titles):
    """公開ページ用に、受講者用ファイルのコピーとダウンロード用の目次を docs/student/ に置く。"""
    import html
    docs.mkdir(parents=True, exist_ok=True)
    for stale in docs.glob("*.lean"):
        if stale.stem not in chapters:
            stale.unlink()
    items = []
    for name in chapters:
        (docs / f"{name}.lean").write_text((OUT / f"{name}.lean").read_text(encoding="utf-8"), encoding="utf-8")
        title = html.escape(titles.get(name, name))
        items.append(f'<li><a href="{name}.lean" download>{name}.lean</a> — {title}</li>')
    (docs / "index.html").write_text(
        '<!DOCTYPE html><html lang="ja"><head><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width, initial-scale=1">'
        '<title>受講者用の Lean ファイル</title>'
        '<style>body{font-family:sans-serif;max-width:50rem;margin:3rem auto;padding:0 1.2rem;line-height:1.9}'
        'li{margin:.5rem 0}</style></head><body>'
        '<h1>受講者用の Lean ファイル</h1>'
        '<p>本文の <code>.lean</code> から解説を省き、コードと練習の問題文だけを残した版です。'
        '説明は<a href="../index.html">HTML 版</a>で読み、手元ではこのファイルでコードを動かしてください。'
        '<code>#check</code> などの結果は載せていないので、予想してから Infoview で確かめましょう。</p>'
        '<p>ファイルは読む順に並んでいます。後のファイルは前のファイルを <code>import</code> するので、'
        'すべて同じ Lean プロジェクトの中に置いてください。</p>'
        '<ol>' + "".join(items) + '</ol></body></html>', encoding="utf-8")
    print(f"  student/ に {len(chapters)} ファイルを公開")


if __name__ == "__main__":
    main()
