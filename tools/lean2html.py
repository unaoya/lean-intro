#!/usr/bin/env python3
"""src/*.lean から講義用 HTML を生成する（依存なし・Python 標準ライブラリのみ）。

使い方:
    python3 tools/lean2html.py

変換規則:
  * `/-! ... -/` ブロック → 地の文（この教材で使う Markdown サブセットを HTML 化）
  * `### 補足` / `### 先取り` → その地の文ブロックを枠で囲む
  * `/-! CALLOUT_START optional|preview -/` から `/-! CALLOUT_END -/` まで
    → コード・出力をまたぐ長い枠（開始・終了マーカー自体は表示しない）
  * 行頭の docstring `/-- ... -/` → 地の文（直後の宣言の説明として、コードの直前に置く）
  * それ以外（宣言・フィールドの docstring・コメント・#check）→ コードブロック（簡易ハイライト付き）

章構成を変えるときは CHAPTERS を書き換えるだけでよい。
"""

import html
import re
from collections import defaultdict, deque
from pathlib import Path

import refs

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"
OUT = ROOT / "docs"

# 章構成（表示順）。*Sol（解答）は単独ページとしては公開しない。
CHAPTERS = ["Intro1", "CH", "Intro2", "Top", "Extra"]

# ✏ 練習に折りたたみで埋め込む解答ファイル（`/-! SOL 固定ラベル:問題番号 -/` 区切り）。
# 問題と解答の数・節内の順序が合わなければ生成をエラーで止める。
SOL_FILES = {"Intro1": "Intro1Sol", "CH": "CHSol", "Intro2": "Intro2Sol", "Top": "TopSol"}

SITE_TITLE = "Lean 4 で書く位相空間 — ミニ教材"
SITE_CONCEPT = (
    "<em>Lean for the Working Mathematician in the Age of AI</em> — "
    "AI がコードを書く時代の、働く数学者のための Lean 入門。"
    "Lean のコードを自分で書けるようになることは目標ではない（それは AI に任せてよい）。"
)
SITE_GOALS = (
    "<p>この教材（Intro1 → CH → Intro2 → Top の4ファイル）の目標は2つある。</p>"
    "<ul>"
    "<li><strong>目標1 — Lean を読めるようになる</strong>。Lean のコードを読むとは、"
    "書かれた<strong>項の型を推測する</strong>ことである。そしてこの推測は"
    "<strong>機械的な手順</strong>で実行できる——だからコンピュータにも実行できる。"
    "実際に自分の手で型を推測できるようになること、少なくとも"
    "「これなら機械にもできそうだ」という感覚を持つことを目指す。</li>"
    "<li><strong>目標2 — 検証の仕組みを納得する</strong>。項の型を推測するこの仕組みが、"
    "<strong>定理の証明の検証にそのまま使える</strong>ことを納得する。"
    "「なぜそれで証明の正しさを検証したと思えるのか」への答えがここにある。</li>"
    "</ul>"
    "<p>目標1が主に Intro1 の、目標2が CH の担当。Intro2 で Top のための"
    "道具（class・Fin・集合・記法）を揃え、Top では現物の数学（位相空間の主定理）に"
    "ついて両方を実感する。その先で、形式化を自分の研究に役立てる可能性を考えたい。"
    "Lean を網羅的に紹介することは目的ではなく、必要な最低限の機能しか説明しない。</p>"
)
SITE_NOTE = (
    "読む順は Intro1 → CH → Intro2 → Top（→ 演習 Extra）。"
    "各 ✏ 練習には折りたたみの解答が付いている（解答もすべて Lean の検査済み）。"
    "ソースは <a href=\"https://github.com/unaoya/lean-intro\">GitHub</a> の "
    "<code>src/*.lean</code>（このページはそこから自動生成）。"
)

# ---------------------------------------------------------------- inline md

def inline(text: str, chapter: str = "", sections=None) -> str:
    """インライン要素: `code` と **bold**。
    bold はコード片を中に含んでよいので、コードを一旦プレースホルダに退避してから
    bold を処理し、最後に戻す。コード内の ** はそのまま残る。"""
    codes: list[str] = []

    def stash(m: re.Match) -> str:
        if m['ref'] is not None:
            value = inline(m['text'])
            if sections is not None and m['label'] in sections:
                value = f'<a href="{refs.href(m["label"], chapter, sections)}">{value}</a>'
        elif m['double'] is not None:
            value = "<code>" + html.escape(re.fullmatch(r"``\s?(.*?)\s?``", m['double'])[1]) + "</code>"
        else:
            value = "<code>" + html.escape(m['code'][1:-1]) + "</code>"
        codes.append(value)
        return f"\x00{len(codes) - 1}\x00"

    tokens = r"(?P<double>``\s?.*?\s?``)|(?P<ref>" + refs.REF_RE.pattern + r")|(?P<code>`[^`]*`)"
    tmp = re.sub(tokens, stash, text)
    e = html.escape(tmp)
    e = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", e)
    return re.sub(r"\x00(\d+)\x00", lambda m: codes[int(m.group(1))], e)

# ---------------------------------------------------------------- prose (md subset)

def smart_join(parts: list[str]) -> str:
    """日本語の折返しは区切りなしで連結するが、行境界のどちらかが
    英数字やコード（バッククォート）のときは空白を1つ入れる。"""
    out = parts[0] if parts else ""
    # Link brackets and destinations do not participate in visible line boundaries.
    visible = refs.stripped("\n".join(parts)).split("\n")
    shown = visible[0]
    for nxt, next_shown in zip(parts[1:], visible[1:]):
        space = " " if shown and next_shown and (
            re.match(r"[A-Za-z0-9`*]", shown[-1]) or re.match(r"[A-Za-z0-9`*]", next_shown[0])
        ) else ""
        out += space + nxt
        shown += space + next_shown
    return out


def render_prose(lines: list[str], chapter: str = "", sections=None, *, section_ids: bool = True) -> str:
    def md(text):
        return inline(text, chapter, sections)

    out = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        if line.strip() == "":
            i += 1
            continue
        # 見出し
        m = re.match(r"^(#{1,4}) (.*)$", line)
        if m:
            level = len(m.group(1))
            heading = refs.HEADING_RE.fullmatch(line)
            attr = f' id="sec-{heading["label"]}"' if heading and section_ids else ""
            title = f'{heading["number"]}. {heading["title"]}' if heading else m.group(2)
            out.append(f"<h{level}{attr}>{md(title)}</h{level}>")
            i += 1
            continue
        # 表
        if line.lstrip().startswith("|"):
            rows = []
            while i < n and lines[i].lstrip().startswith("|"):
                rows.append([c.strip() for c in lines[i].strip().strip("|").split("|")])
                i += 1
            out.append("<table>")
            if len(rows) >= 2 and all(re.fullmatch(r":?-+:?", c) for c in rows[1]):
                out.append("<thead><tr>" + "".join(f"<th>{md(c)}</th>" for c in rows[0]) + "</tr></thead>")
                body = rows[2:]
            else:
                body = rows
            out.append("<tbody>")
            for r in body:
                out.append("<tr>" + "".join(f"<td>{md(c)}</td>" for c in r) + "</tr>")
            out.append("</tbody></table>")
            continue
        # 4字下げの引用コード（間の空行は、次も字下げなら取り込む）
        if line.startswith("    "):
            code = []
            while i < n:
                if lines[i].startswith("    "):
                    code.append(lines[i][4:])
                    i += 1
                elif lines[i].strip() == "":
                    j = i
                    while j < n and lines[j].strip() == "":
                        j += 1
                    if j < n and lines[j].startswith("    "):
                        code.extend([""] * (j - i))
                        i = j
                    else:
                        break
                else:
                    break
            out.append('<pre class="quote"><code>' + html.escape(refs.stripped("\n".join(code))) + "</code></pre>")
            continue
        # リスト（* / 1. 、2字下げで入れ子と継続行）
        if re.match(r"^ *(\*|\d+\.) ", line):
            i, block = render_list(lines, i, chapter, sections)
            out.append(block)
            continue
        # 段落（日本語の折返しなので区切りなしで連結）
        para = []
        while i < n and lines[i].strip() != "" and not re.match(r"^(#{1,4} |\||    | *(\*|\d+\.) )", lines[i]):
            para.append(lines[i].strip())
            i += 1
        out.append(f"<p>{md(smart_join(para))}</p>")
    return "\n".join(out)


def render_list(lines: list[str], i: int, chapter: str = "", sections=None) -> tuple[int, str]:
    """インデント幅で入れ子を判定する簡易リストパーサ。"""
    items = []  # (indent, kind, [text])
    n = len(lines)
    while i < n:
        m = re.match(r"^( *)(\*|\d+\.) (.*)$", lines[i])
        if m:
            indent = len(m.group(1))
            kind = "ul" if m.group(2) == "*" else "ol"
            items.append((indent, kind, [m.group(3)]))
            i += 1
        elif lines[i].strip() != "" and lines[i].startswith("  ") and items:
            items[-1][2].append(lines[i].strip())  # 継続行
            i += 1
        else:
            break

    def build(pos: int, level_indent: int) -> tuple[int, str]:
        kind = items[pos][1]
        out = [f"<{kind}>"]
        while pos < len(items):
            indent, k, texts = items[pos]
            if indent < level_indent or (indent == level_indent and k != kind):
                break
            if indent > level_indent:
                pos, sub = build(pos, indent)
                out[-1] = out[-1][:-5] + sub + "</li>"  # 直前の </li> の中に入れる
                continue
            out.append("<li>" + inline(smart_join(texts), chapter, sections) + "</li>")
            pos += 1
        out.append(f"</{kind}>")
        return pos, "\n".join(out)

    _, html_out = build(0, items[0][0])
    return i, html_out

# ---------------------------------------------------------------- code highlight

KEYWORDS = (
    "def|theorem|lemma|example|instance|structure|class|inductive|where|"
    "fun|match|with|by|have|let|show|intro|exact|refine|apply|constructor|"
    "cases|using|rw|by_cases|obtain|calc|universe|variable|namespace|end|"
    "section|open|export|import|syntax|macro_rules|macro|prefix|infixl|"
    "infixr|postfix|noncomputable|deriving|attribute|axiom|sorry"
)
# 1パスで全トークンを拾う（逐次置換だと、挿入した span の中の
# `class` などの語が次の置換に誤マッチしてタグを壊す）
TOKEN_RE = re.compile(
    r"(?P<cmd>#check|#print|#eval|#guard)"
    r"|(?<![\w_.'])(?P<kw>" + KEYWORDS + r")(?![\w_'])"
    r"|(?<![\w_.'])(?P<sort>Type|Prop|Sort)(?![\w_'])"
)


def _token_repl(m: re.Match) -> str:
    if m.group("cmd"):
        return f'<span class="kw">{m.group("cmd")}</span>'
    if m.group("kw"):
        w = m.group("kw")
        cls = "sorry" if w == "sorry" else "kw"
        return f'<span class="{cls}">{w}</span>'
    return f'<span class="sort">{m.group("sort")}</span>'


def hl_code_part(code: str) -> str:
    """コード片（コメント以外）のハイライト。エスケープしてから1パスで span を差す。"""
    return TOKEN_RE.sub(_token_repl, html.escape(code))


COMMENT_BOLD_RE = re.compile(r"\*\*([^*]+?)\*\*")


def esc_comment(text: str) -> str:
    """コメント・docstring 用: エスケープした上で **…** を太字にする（行内のみ）。"""
    return COMMENT_BOLD_RE.sub(r"<strong>\1</strong>", html.escape(text))


def render_code(lines: list[str]) -> str:
    out = []
    in_doc = False
    for line in refs.stripped("\n".join(lines)).split("\n"):
        if in_doc:
            out.append(f'<span class="doc">{esc_comment(line)}</span>')
            if "-/" in line:
                in_doc = False
            continue
        if line.lstrip().startswith("/--"):
            out.append(f'<span class="doc">{esc_comment(line)}</span>')
            if "-/" not in line:
                in_doc = True
            continue
        idx = line.find("--")
        if idx >= 0:
            code, comment = line[:idx], line[idx:]
            out.append(hl_code_part(code) + f'<span class="cm">{esc_comment(comment)}</span>')
        else:
            out.append(hl_code_part(line))
    return '<pre class="lean"><code>' + "\n".join(out) + "</code></pre>"

# ---------------------------------------------------------------- file parsing

def parse(path: Path, *, with_line_numbers: bool = False) -> list:
    """ファイルを (kind, lines) のセグメント列に分ける。
    kind は 'prose'（/-! ブロック）・'doc'（行頭の docstring）・'code' のいずれか。
    インデントされた docstring（structure のフィールドなど）は宣言の一部なので
    code に残す。with_line_numbers=True では (kind, 開始行番号, lines) を返す。"""
    lines = path.read_text(encoding="utf-8").split("\n")
    segments = []
    cur_kind, cur = None, []
    cur_start = 0

    def flush():
        nonlocal cur_kind, cur, cur_start
        if cur_kind == "code":
            while cur and cur[0].strip() == "":
                cur.pop(0)
                cur_start += 1
            while cur and cur[-1].strip() == "":
                cur.pop()
        if cur_kind and cur:
            segments.append((cur_kind, cur_start + 1, cur) if with_line_numbers else (cur_kind, cur))
        cur_kind, cur = None, []

    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("/-!") or line.startswith("/--"):
            kind = "prose" if line.startswith("/-!") else "doc"
            flush()
            cur_start = i
            body = [line[3:].lstrip()]
            while "-/" not in body[-1] and i + 1 < len(lines):
                i += 1
                body.append(lines[i])
            # 閉じ `-/` を除去（行末どちらのスタイルにも対応）
            body[-1] = body[-1][: body[-1].rfind("-/")].rstrip()
            cur_kind, cur = kind, [b for b in body]
            flush()
        else:
            if cur_kind != "code":
                flush()
                cur_kind = "code"
                cur_start = i
            cur.append(line)
        i += 1
    flush()
    return segments


SOL_MARK_RE = refs.SOL_RE


def parse_solutions(path: Path) -> list[tuple[tuple[str, int], list[tuple[str, list[str]]]]]:
    """解答ファイルを `/-! SOL 固定ラベル:問題番号 -/` ごとに分ける。
    最初のマーカーより前（import・ファイル頭の説明）は捨てる。"""
    sols = []
    cur_label, cur_segs = None, []
    for kind, lines in parse(path):
        m = SOL_MARK_RE.match(lines[0].strip()) if kind == "prose" and lines else None
        if m and all(not l.strip() for l in lines[1:]):
            if cur_label is not None:
                sols.append((cur_label, cur_segs))
            cur_label, cur_segs = (m['label'], int(m['item'])), []
        elif cur_label is not None:
            cur_segs.append((kind, lines))
    if cur_label is not None:
        sols.append((cur_label, cur_segs))
    return sols


EXERCISE_HEAD_RE = re.compile(r"^#{2,4} .*✏ 練習")
ITEM_RE = re.compile(r"^(\d+)\. ")
CALLOUT_HEAD_RE = re.compile(r"^### (補足|先取り)(?:[（:]|$)")
CALLOUT_START_RE = re.compile(r"^CALLOUT_START (optional|preview)$")
CALLOUT_END = "CALLOUT_END"


def render_chapter(name: str, segments, sections=None) -> str:
    """本文をレンダリングする。長い注記は CALLOUT_START/END でコードごと囲む。"""
    sol_path = SRC / f"{SOL_FILES[name]}.lean" if name in SOL_FILES else None
    sols = parse_solutions(sol_path) if sol_path and sol_path.exists() else None
    queues = defaultdict(deque)
    for (label, item), solution in sols or []:
        queues[label].append((item, solution))
    body = []
    sec, sol_i = None, 0
    active_callout = None
    for kind, lines in segments:
        first = next((l.strip() for l in lines if l.strip()), "")
        if kind == "prose" and (start := CALLOUT_START_RE.fullmatch(first)):
            if active_callout is not None or sum(bool(l.strip()) for l in lines) != 1:
                raise SystemExit(f"error: {name}: invalid nested CALLOUT_START")
            active_callout = start.group(1)
            body.append(f'<aside class="note note--{active_callout}">')
            continue
        if kind == "prose" and first == CALLOUT_END:
            if active_callout is None or sum(bool(l.strip()) for l in lines) != 1:
                raise SystemExit(f"error: {name}: unexpected CALLOUT_END")
            body.append("</aside>")
            active_callout = None
            continue
        if kind == "code":
            body.append(render_code(lines))
            continue
        if kind == "doc":
            body.append(render_prose(lines, name, sections, section_ids=False))
            continue
        for l in lines:
            m = refs.HEADING_RE.fullmatch(l)
            if m:
                sec = m['label']
            elif l.startswith("## "):
                sec = None
        rendered = render_prose(lines, name, sections)
        callout = CALLOUT_HEAD_RE.match(first)
        if callout and active_callout is None:
            kind = "optional" if callout.group(1) == "補足" else "preview"
            rendered = f'<aside class="note note--{kind}">{rendered}</aside>'
        body.append(rendered)
        if sols is None or not any(EXERCISE_HEAD_RE.match(l) for l in lines):
            continue
        for item in [int(m.group(1)) for l in lines if (m := ITEM_RE.match(l))]:
            label = f"{sec}:{item}"
            if not queues[sec]:
                raise SystemExit(f"error: {name} 練習 {label} の解答がない（{SOL_FILES[name]}.lean）")
            got, segs2 = queues[sec].popleft()
            sol_i += 1
            if got != item:
                raise SystemExit(f"error: {name} 練習 {label} の位置に SOL {got}（{SOL_FILES[name]}.lean の順序を確認）")
            inner = "\n".join(render_code(ls) if k == "code" else render_prose(ls, name, sections, section_ids=False) for k, ls in segs2)
            body.append(f'<details class="sol"><summary>解答 {item}</summary>\n{inner}\n</details>')
    if active_callout is not None:
        raise SystemExit(f"error: {name}: CALLOUT_END is missing")
    if sols is not None and sol_i != len(sols):
        raise SystemExit(f"error: {name} で解答が {len(sols) - sol_i} 個余っている（{SOL_FILES[name]}.lean）")
    return "\n".join(body)


def chapter_title(segments) -> str:
    for kind, lines in segments:
        if kind == "prose":
            for l in lines:
                m = re.match(r"^# (.*)$", l)
                if m:
                    return m.group(1)
    return "無題"

# ---------------------------------------------------------------- page template

LIGHT_VARS = """
:root { --fg: #1a1a1a; --bg: #ffffff; --code-bg: #f5f5f0; --border: #ddd;
        --kw: #7b2d8b; --doc: #1a7f37; --cm: #8a8a8a; --sort: #0550ae; --sorry: #c0392b;
        --link: #0969da; --quote-bg: #f0f4f8;
        --optional-bg: #f6f6f2; --optional-border: #666666; --optional-fg: #242424;
        --preview-bg: #f3f0f8; --preview-border: #5a4271; --preview-fg: #2a2036; }
"""

DARK_VARS = """
@media (prefers-color-scheme: dark) {
  :root { --fg: #d8d8d3; --bg: #1e1e1e; --code-bg: #262626; --border: #444;
          --kw: #d38ae0; --doc: #7ec699; --cm: #888; --sort: #6cb6ff; --sorry: #e07a6a;
          --link: #58a6ff; --quote-bg: #24292e;
          --optional-bg: #2b2b29; --optional-border: #a3a3a0; --optional-fg: #e3e3df;
          --preview-bg: #2b2533; --preview-border: #bca6d4; --preview-fg: #eee8f5; }
}
"""

BASE_CSS = """
* { box-sizing: border-box; }
body { color: var(--fg); background: var(--bg); margin: 0;
       font-family: "Hiragino Sans", "Noto Sans CJK JP", sans-serif;
       line-height: 1.9; font-size: 16px; }
main { max-width: 50rem; margin: 0 auto; padding: 1rem 1.2rem 4rem; }
h1 { font-size: 1.7rem; border-bottom: 2px solid var(--border); padding-bottom: .4rem; }
h2 { font-size: 1.35rem; margin-top: 2.5rem; border-bottom: 1px solid var(--border);
     padding-bottom: .25rem; }
h3 { font-size: 1.1rem; margin-top: 2rem; }
p { margin: .8rem 0; }
code { font-family: "SF Mono", "JetBrains Mono", Menlo, Consolas, monospace;
       font-size: .88em; background: var(--code-bg); padding: .1em .3em;
       border-radius: 4px; }
pre { background: var(--code-bg); border: 1px solid var(--border); border-radius: 8px;
      padding: .8rem 1rem; overflow-x: auto; line-height: 1.55; }
pre code { background: none; padding: 0; font-size: .85rem; }
pre.quote { background: var(--quote-bg); }
aside.note { margin: 1.3rem 0; padding: .7rem 1rem; border-radius: 8px; }
aside.note h3 { margin: 0 0 .35rem; font-size: 1rem; }
aside.note p { margin: .4rem 0; }
aside.note--optional { color: var(--optional-fg); background: var(--optional-bg);
                       border: 2px dashed var(--optional-border); }
aside.note--preview { color: var(--preview-fg); background: var(--preview-bg);
                      border: 1px solid var(--preview-border);
                      border-left: 6px solid var(--preview-border); }
.kw { color: var(--kw); font-weight: 600; }
.doc { color: var(--doc); }
.cm { color: var(--cm); }
.sort { color: var(--sort); }
.sorry { color: var(--sorry); font-weight: 700; }
table { border-collapse: collapse; margin: 1rem 0; display: block; overflow-x: auto; }
th, td { border: 1px solid var(--border); padding: .35rem .7rem; }
th { background: var(--code-bg); }
ul, ol { padding-left: 1.6rem; }
li { margin: .25rem 0; }
nav { display: flex; justify-content: space-between; max-width: 50rem;
      margin: 0 auto; padding: .8rem 1.2rem; font-size: .92rem; }
nav a { color: var(--link); text-decoration: none; }
nav a:hover { text-decoration: underline; }
a { color: var(--link); }
hr { border: none; border-top: 1px solid var(--border); }
details.sol { margin: .6rem 0 1.4rem; border: 1px solid var(--border); border-radius: 8px;
              padding: .35rem .9rem; background: var(--code-bg); }
details.sol > summary { cursor: pointer; color: var(--link); font-weight: 600; }
details.sol[open] > summary { margin-bottom: .4rem; }
"""

# 印刷（PDF）用の上書き。色はライト固定、章の頭で改ページ、
# コードは横スクロールできないので折り返す。
PRINT_CSS = """
:root { color-scheme: light; }
@page { size: A4; margin: 17mm 15mm; }
html { font-size: 10.5pt; }
body { font-size: 1rem; line-height: 1.75; }
main { max-width: none; padding: 0; }
section.chapter { page-break-before: always; break-before: page; }
section.chapter:first-of-type { page-break-before: avoid; break-before: auto; }
h1, h2, h3, h4 { page-break-after: avoid; break-after: avoid; }
h1 { margin-top: 0; }
pre { white-space: pre-wrap; overflow-wrap: break-word; overflow: visible; }
table { display: table; width: 100%; }
details.sol > summary { list-style: none; }
details.sol > summary::-webkit-details-marker { display: none; }
a { text-decoration: none; }
"""

CSS = LIGHT_VARS + DARK_VARS + BASE_CSS
PDF_CSS = LIGHT_VARS + BASE_CSS + PRINT_CSS


def nav_html(idx: int) -> str:
    prev_a = ""
    next_a = ""
    if idx > 0:
        prev_a = f'<a href="{CHAPTERS[idx-1].lower()}.html">← {CHAPTERS[idx-1]}</a>'
    if idx + 1 < len(CHAPTERS):
        next_a = f'<a href="{CHAPTERS[idx+1].lower()}.html">{CHAPTERS[idx+1]} →</a>'
    return f'<nav><span>{prev_a}</span><a href="index.html">目次</a><span>{next_a}</span></nav>'


def page(title: str, body: str, nav: str = "", css: str = CSS) -> str:
    return f"""<!DOCTYPE html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)}</title>
<style>{css}</style>
</head>
<body>
{nav}
<main>
{body}
</main>
{nav}
</body>
</html>
"""

ROLES = {
    "Intro1": "コードの読み方の基礎（項と型、関数、帰納型、structure）",
    "CH": "証明が検査される仕組み",
    "Intro2": "CH のあとに読む後編（class・Fin・集合の正体・記法の自作）",
    "Top": "現物の数学が形式化される様子（主定理: コンパクト→ハウスドルフの連続全単射は同相）",
    "Extra": "演習（sorry を自分で埋める）",
}


def toc_html(titles: dict, href) -> str:
    """目次。`href(name)` がリンク先を返す（HTML は別ページ、PDF は同一文書内アンカー）。"""
    out = [f"<h1>{html.escape(SITE_TITLE)}</h1>",
           f"<p>{SITE_CONCEPT}</p>", SITE_GOALS, f"<p>{SITE_NOTE}</p>", "<ol>"]
    for name in CHAPTERS:
        role = ROLES.get(name, "")
        suffix = f" — {role}" if role else ""
        out.append(f'<li><a href="{href(name)}">{inline(titles[name])}</a>{suffix}</li>')
    out.append("</ol>")
    return "\n".join(out)

# ---------------------------------------------------------------- pdf

PDF_OUT = ROOT / "pdf" / "all.pdf"

# Chrome を探す順。環境変数 CHROME で明示的に上書きできる。
CHROME_CANDIDATES = [
    "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
    "/Applications/Chromium.app/Contents/MacOS/Chromium",
    "/Applications/Microsoft Edge.app/Contents/MacOS/Microsoft Edge",
    "google-chrome", "chromium", "chromium-browser", "msedge",
]


def find_chrome() -> str | None:
    import os
    import shutil
    env = os.environ.get("CHROME")
    if env:
        return env if Path(env).exists() or shutil.which(env) else None
    for cand in CHROME_CANDIDATES:
        if cand.startswith("/"):
            if Path(cand).exists():
                return cand
        elif (found := shutil.which(cand)):
            return found
    return None


def pdf_html(titles: dict, bodies: dict) -> str:
    """全章を1つの印刷用 HTML にまとめる。練習の解答はすべて開いた状態にする。"""
    parts = [f'<section class="chapter" id="ch-index">\n{toc_html(titles, lambda n: f"#ch-{n.lower()}")}\n</section>']
    for name in CHAPTERS:
        body = bodies[name].replace('<details class="sol">', '<details class="sol" open>')
        # Stable labels are globally unique, including in the combined document.
        body = re.sub(r'href="(?:[a-z0-9]+\.html)?#(sec-[A-Za-z0-9_.-]+)"', r'href="#\1"', body)
        parts.append(f'<section class="chapter" id="ch-{name.lower()}">\n{body}\n</section>')
    return page(SITE_TITLE, "\n".join(parts), css=PDF_CSS)


def build_pdf(titles: dict, bodies: dict) -> None:
    """印刷用 HTML を headless Chrome に刷らせて pdf/all.pdf を作る。"""
    import subprocess
    import tempfile
    chrome = find_chrome()
    if chrome is None:
        print("  PDF: Chrome が見つからないので省略（環境変数 CHROME で指定できる）")
        return
    PDF_OUT.parent.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory() as tmp:
        src = Path(tmp) / "all.html"
        src.write_text(pdf_html(titles, bodies), encoding="utf-8")
        cmd = [chrome, "--headless=new", "--disable-gpu", "--no-sandbox",
               f"--print-to-pdf={PDF_OUT}", "--no-pdf-header-footer", src.as_uri()]
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
    if r.returncode != 0 or not PDF_OUT.exists():
        print(f"  PDF: 生成に失敗（exit {r.returncode}）\n{r.stderr.strip()}")
        return
    print(f"  pdf/all.pdf 生成（{PDF_OUT.stat().st_size / 1e6:.1f} MB）")

# ---------------------------------------------------------------- main

def main(with_pdf: bool = True):
    references = refs.analyze(SRC, CHAPTERS, SOL_FILES, parse)
    if references.errors:
        raise SystemExit("\n".join(references.errors))
    try:
        for path in references.write():
            print(f"  {path.name}: 節番号・参照を更新")
    except (OSError, ValueError) as exc:
        raise SystemExit(str(exc)) from exc
    titles, bodies = {}, {}
    for name in CHAPTERS:
        segments = parse(SRC / f"{name}.lean")
        titles[name] = chapter_title(segments)
        bodies[name] = render_chapter(name, segments, references.sections)
    OUT.mkdir(exist_ok=True)
    (OUT / ".nojekyll").write_text("")
    for idx, name in enumerate(CHAPTERS):
        out_path = OUT / f"{name.lower()}.html"
        out_path.write_text(page(titles[name], bodies[name], nav_html(idx)), encoding="utf-8")
        print(f"  {name}.lean → docs/{name.lower()}.html")

    (OUT / "index.html").write_text(
        page(SITE_TITLE, toc_html(titles, lambda n: f"{n.lower()}.html")), encoding="utf-8")
    print("  index.html 生成")

    if with_pdf:
        build_pdf(titles, bodies)


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser(description="src/*.lean → docs/*.html（＋ pdf/all.pdf）")
    ap.add_argument("--no-pdf", action="store_true", help="PDF を作らず HTML だけ生成する")
    main(with_pdf=not ap.parse_args().no_pdf)
