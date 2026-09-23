#!/usr/bin/env python3
"""開発用の本文 dev/src/*.lean から、受講者用のファイル一式をリポジトリ直下に作る。

受講の想定: テキストは Web ページ（docs/）で読み、VS Code でリポジトリ直下を開いて
Lean のファイルを動かす。直下は受講者用の Lake プロジェクトで、次のものを置く。

  LeanIntro/Original/   受講者用ファイル（解説を省いた版。直接は書き込まない）
  LeanIntro/Solutions/  解答（解説を省いた版）
  LeanIntro/MyWork/     書き込み用（git 管理外。lakefile.lean が Original/ から自動で作る）
  LeanIntro/Status.lean Start.lean から使う、準備と更新の確認
  Start.lean            最初に開く確認用ファイル
  lakefile.lean         受講者用プロジェクトの設定（MyWork/ の自動作成を含む）

lakefile・Start・Status のひな形は tools/student/ にある。

受講者用ファイルでは、コード・節見出し・練習の問題文（番号は HTML と同じ通し番号）を残し、
地の文・docstring・出力の表示ブロックを消す。地の文の中のコード例はコメントアウトして残す。

使い方（dev/ で）:
    python3 tools/student.py   # 通常は lean2html.py から呼ばれる
    lake -d .. build           # 受講者用プロジェクトがコンパイルできるか検査
"""

from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from render_support import parse  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent   # dev/
REPO = ROOT.parent                               # リポジトリ直下（受講者用プロジェクト）
SRC = ROOT / "src"
ASSETS = Path(__file__).resolve().parent / "student"   # lakefile・Start・Status のひな形
LESSONS = REPO / "LeanIntro"
ORIGINAL = LESSONS / "Original"
SOLUTIONS = LESSONS / "Solutions"
ITEM_RE = re.compile(r"^(\d+)\. ")
IMPORT_RE = re.compile(r"^import «(\d\d_\w+?)(Sol)?»", re.M)

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


def prose_to_student(lines, after_command: bool, in_callout: bool = False, counter=None):
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
        rows = body[heading[0] + 1:]
        if counter is not None:     # HTML と同じ通し番号にする
            rows = [ITEM_RE.sub(lambda m: f"{counter.next()}. ", r) if ITEM_RE.match(r) else r for r in rows]
        text = "\n".join(rows).strip("\n")
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


class Counter:
    def __init__(self, start: int):
        self.value = start

    def next(self) -> int:
        self.value += 1
        return self.value - 1


def student_file(path: Path, counter: "Counter | None" = None) -> str:
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
            out.extend(prose_to_student(lines, after_command, in_callout, counter))
            after_command = False
        # docstring は捨てる
    return tidy(out)


def tidy(out) -> str:
    # 中身（コード・練習・例）が1つもない小見出しは出さない
    end = "-- （補足・先取りここまで）"
    kept, skip_end = [], False
    for i, line in enumerate(out):
        if line == end and skip_end:
            skip_end = False
            continue
        if line.startswith("-- ### "):
            rest = next((l for l in out[i + 1:] if l.strip()), "")
            if rest.startswith("-- #"):
                continue
            if rest == end:           # 中身のない枠は、見出しも終わりの印も出さない
                skip_end = True
                continue
        kept.append(line)
    text = "\n".join(kept)
    return re.sub(r"\n{3,}", "\n\n", text).strip() + "\n"


def relocate_imports(text: str) -> str:
    """本文の `import «02_Forall»` を、受講者用プロジェクトの Original/ のモジュールに向ける。"""
    return IMPORT_RE.sub(lambda m: f"import LeanIntro.Original.«{m[1]}»", text)


def exercise_numbers(path: Path, start: int, lean2html) -> dict:
    """本文の練習に、HTML と同じ通し番号を対応させる。
    同じ節に練習のブロックが複数あると節内の問題番号が1から振り直されるので、
    HTML の生成と同じく「節ラベルごとに出現順」で対応させる（節ラベル → [(問題番号, 通し番号), …]）。"""
    import refs
    from collections import defaultdict, deque
    numbers, number, sec = defaultdict(deque), start, None
    for kind, lines in parse(path):
        if kind != "prose":
            continue
        for line in lines:
            m = refs.HEADING_RE.fullmatch(line)
            if m:
                sec = m['label']
            elif line.startswith("## "):
                sec = None
        for item, _ in lean2html.exercise_parts(lines):
            if item is not None:
                numbers[sec].append((item, number))
                number += 1
    return numbers


def solution_file(path: Path, numbers: dict) -> str:
    """解答ファイルから、コードと「どの練習の解答か」の見出しだけを残す。"""
    import refs
    out = []
    for kind, lines in parse(path):
        text = [l.strip() for l in lines if l.strip()]
        if kind == "prose" and len(text) == 1 and (m := refs.SOL_RE.fullmatch(text[0])):
            label, item = m.group("label"), int(m.group("item"))
            queue = numbers.get(label)
            if not queue or queue[0][0] != item:
                raise SystemExit(f"error: {path.name}: SOL {label}:{item} に対応する練習が本文にない")
            out += ["", f"-- ✏ 練習 {queue.popleft()[1]} の解答", ""]
        elif kind == "code":
            out += lines + [""]
    return re.sub(r"\n{3,}", "\n\n", "\n".join(out)).strip() + "\n"


ORIGINAL_HEADER = (
    "-- 受講者用ファイル（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。\n"
    "-- このファイルには書き込まず、LeanIntro/MyWork/ の同じ名前のファイルを使うこと。\n\n")
SOLUTION_HEADER = (
    "-- 解答（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。\n\n")


def main():
    sys.path.insert(0, str(ROOT / "tools"))
    import lean2html
    import refs
    chapters = lean2html.CHAPTERS
    ORIGINAL.mkdir(parents=True, exist_ok=True)
    SOLUTIONS.mkdir(parents=True, exist_ok=True)
    start = 1
    solutions = []
    for name in chapters:
        path = SRC / f"{name}.lean"
        count = lean2html.exercise_count(parse(path))
        text = relocate_imports(student_file(path, Counter(start)))
        (ORIGINAL / f"{name}.lean").write_text(ORIGINAL_HEADER + text, encoding="utf-8")
        sol = SRC / f"{name}Sol.lean"
        if sol.exists():
            if re.search(r"^/-! SOL ", sol.read_text(encoding="utf-8"), re.M):   # 練習ごとの解答の形式
                body = solution_file(sol, exercise_numbers(path, start, lean2html))
            else:   # 演習の章: 解答は sorry を埋めた全文
                body = student_file(sol)
            (SOLUTIONS / f"{name}.lean").write_text(SOLUTION_HEADER + relocate_imports(body), encoding="utf-8")
            solutions.append(name)
        start += count
        print(f"  LeanIntro/Original/{name}.lean" + ("（解答あり）" if sol.exists() else ""))
    for folder, keep in [(ORIGINAL, chapters), (SOLUTIONS, solutions)]:
        for stale in folder.glob("*.lean"):
            if stale.stem not in keep:
                stale.unlink()
    for target_name, template in [("Status.lean", "status.lean"), ("Start.lean", "start.lean"),
                                  ("lakefile.lean", "lakefile.lean")]:
        text = (ASSETS / template).read_text(encoding="utf-8").replace("@@CHAPTERS@@", " ".join(chapters))
        (LESSONS / target_name if target_name == "Status.lean" else REPO / target_name).write_text(
            text, encoding="utf-8")


if __name__ == "__main__":
    main()
