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
  * 地の文の `$…$` / `$$…$$` → 数式（KaTeX を CDN から読み込み、閲覧時に描画）
  * 字下げブロックが「前提行 / ---- / 結論行」の3行 → 推論規則（横線付き。前提は空白2つ以上で区切る）

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
CHAPTERS = ["Intro1a", "CH1", "Intro1b", "CH2", "Intro2", "Top", "Extra", "Ascoli"]

# ✏ 練習に折りたたみで埋め込む解答ファイル（`/-! SOL 固定ラベル:問題番号 -/` 区切り）。
# 問題と解答の数・節内の順序が合わなければ生成をエラーで止める。
SOL_FILES = {name: name + "Sol" for name in CHAPTERS if name not in ("Extra", "Ascoli")}

SITE_TITLE = "はじめての Lean"
SITE_CONCEPT = (
    "この教材の目的は、Lean のコードを<strong>書ける</strong>ようになることではなく、"
    "証明が検査される<strong>仕組みを納得する</strong>ことである"
    "（書く仕事は AI に任せてよい）。"
)
SITE_GOALS = (
    "<h2>目標</h2>"
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
    "<p>この2つの目標に向けて、Intro1a・Intro1b で次の3段階を学ぶ。</p>"
    "<ul>"
    "<li><strong>型がどのように作られるか</strong>を知る。</li>"
    "<li>その型の<strong>項をどのように作り、使うか</strong>を知る。</li>"
    "<li>複雑な項についても、<strong>部分項から順に型を推測できる</strong>ようになる。</li>"
    "</ul>"
    "<p>CH1・CH2 では、「<strong>命題は型であり、証明はその型の項である</strong>」"
    "という対応を学ぶ。これによって、目標1の「項の型を推測する」仕組みが、"
    "目標2の「証明を検証する」仕組みへ接続する。</p>"
    "<h2>仕組みのスローガン</h2>"
    "<p>納得したいことは、突き詰めれば次の2つである。</p>"
    "<ol>"
    "<li>文字列が<strong>項</strong>であるかどうかは、機械的に判定できる。</li>"
    "<li>項が与えられたら、<strong>型</strong>が付くかどうかを機械的に判定でき、"
    "付く場合はその型を計算できる。</li>"
    "</ol>"
    "<p>対象は「文字列」と「その中の項」という2層だけで済む。"
    "「項」を「文法規則に従って作られる文字列」と定義するのだから、"
    "①の「項である」＝「文法規則に従っている」は定義そのものである。"
    "ただし、数字 <code>2</code> のような記法は、文字列の段階ではまだ型が決まらず、"
    "置かれた場所で期待される型に応じて <code>Nat</code> とも <code>Int</code> とも"
    "読まれる。①にはこの「読み方を決める」ことも含まれ、②の項は"
    "読み方が決まったあとの項である。"
    "実質は②にあり、この型の判定・計算がそのまま証明の検証になる、"
    "というのが全体の筋である。</p>"
    "<h2>設計の方針</h2>"
    "<ul>"
    "<li><strong>タクティクについて詳しくは説明しない</strong>。Top では、"
    "タクティクを証明項を組み立てるための仕組みとして簡単に紹介し、"
    "タクティクによる証明と、それに対応する項スタイルの証明を比較する。</li>"
    "<li><strong>mathlib は使わず、Lean 4 の標準環境（自動的に読み込まれる"
    " Prelude を含む）だけ</strong>を使う。集合も位相もすべて自作する。</li>"
    "<li>どちらも理由は同じ——<strong>仕組みを納得するために、ブラックボックスを"
    "減らしたい</strong>からである。実際にコードを書く場面では、タクティクも"
    " mathlib も遠慮なく使えばよい。</li>"
    "<li>Lean を網羅的に紹介することは目的ではなく、必要な最低限の機能しか"
    "説明しない。</li>"
    "</ul>"
    "<h2>構成と読む順</h2>"
    "<p>読む順は <strong>Intro1a → CH1 → Intro1b → CH2 → Intro2 → Top"
    "（→ 演習 Extra・Ascoli）</strong>。</p>"
    "<p>型と項の道具を学んだところで、その道具を使う証明を読む。"
    "この往復を2回行い、目標1の「項の型を読む」ことと、"
    "目標2の「証明が検査される仕組みを納得する」ことを段階的につなぐ。</p>"
    "<ol>"
    "<li><strong>1往復目 — 関数から、ならば・全称の証明へ。</strong>"
    "Intro1a で項と型、定義、関数・依存関数、暗黙引数を学ぶ。"
    "続く CH1 では、仮定や対象を受け取り、適用して進む証明を読む。"
    "「単射どうしの合成は単射」の証明まで進み、"
    "型検査が証明の検査になることを確かめる。</li>"
    "<li><strong>2往復目 — 構成子と場合分けから、かつ・または・存在の証明へ。</strong>"
    "Intro1b で帰納型、場合分け・再帰、structure を学び、"
    "項を作る・分解する道具を増やす。続く CH2 では、その道具を使って"
    "「かつ」「または」「矛盾」「存在」の証明を読む。"
    "偶数の和や全射の合成を例に、関数・構成子・場合分けを組み合わせ、"
    "等式の仕組みと証明検査の全体像を整理する。</li>"
    "</ol>"
    "<p>そのあと、Intro2 で Top のための道具"
    "（class・集合・記法）を揃え、Top では現物の数学"
    "（位相空間の主定理: コンパクト空間からハウスドルフ空間への連続全単射は同相）"
    "について両方を実感する。その先で、形式化を自分の研究に役立てる可能性を"
    "考えたい。</p>"
)
SITE_NOTE = (
    "各 ✏ 練習には折りたたみの解答が付いている（解答もすべて Lean の検査済み）。"
    "2往復構成に改める前の旧版は <a href=\"original/index.html\">こちら</a>。"
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
            rule = render_rule(code)
            if rule is not None:
                out.append(rule)
            else:
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


def render_rule(code: list[str]) -> str | None:
    """字下げブロックが「前提行 / ---- / 結論行」の3行なら推論規則として横線付きで組む。
    前提は2つ以上の空白で区切る。該当しなければ None（通常のコード引用として扱う）。"""
    rows = [l for l in code if l.strip()]
    if len(rows) != 3 or not re.fullmatch(r"\s*-{4,}\s*", rows[1]):
        return None
    prems = "".join(f"<span>{html.escape(p)}</span>" for p in re.split(r"\s{2,}", rows[0].strip()))
    return (f'<div class="rule"><div class="prem">{prems}</div>'
            f'<div class="concl">{html.escape(rows[2].strip())}</div></div>')


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

# 地の文の中に入れ子のコメント（`/- … -/`）の例を書けるよう、入れ子を数えて
# `/-! … -/` の終わりを決める版を使う。セグメントの形式は従来と同じ。
from render_support import parse  # noqa: E402


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
.rule { display: inline-grid; text-align: center; margin: 1rem 2rem;
        font-family: "SF Mono", "JetBrains Mono", Menlo, Consolas, monospace; font-size: .85rem; }
.rule .prem { display: flex; gap: 2em; justify-content: center; padding: 0 .5em; }
.rule .concl { border-top: 1px solid var(--fg); padding: .15em .5em 0; }
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


KATEX_VER = "0.18.7"
KATEX_HEAD = f"""<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@{KATEX_VER}/dist/katex.min.css">
<script defer src="https://cdn.jsdelivr.net/npm/katex@{KATEX_VER}/dist/katex.min.js"></script>
<script defer src="https://cdn.jsdelivr.net/npm/katex@{KATEX_VER}/dist/contrib/auto-render.min.js"
  onload="renderMathInElement(document.body,{{delimiters:[{{left:'$$',right:'$$',display:true}},{{left:'$',right:'$',display:false}}]}})"></script>"""


def page(title: str, body: str, nav: str = "", css: str = CSS) -> str:
    return f"""<!DOCTYPE html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)}</title>
<style>{css}</style>
{KATEX_HEAD}
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
    "Intro1a": "項と型・関数・依存関数・暗黙引数",
    "CH1": "ならば・全称・単射の合成・証明検査の核心",
    "Intro1b": "帰納型・場合分け・再帰・structure",
    "CH2": "組と場合分け・存在・偶数と全射・検査の詳説",
    "Intro2": "位相空間を読むための道具（class・集合の正体・記法の自作）",
    "Top": "現物の数学が形式化される様子（主定理: コンパクト→ハウスドルフの連続全単射は同相）",
    "Extra": "演習（sorry を自分で埋める）",
    "Ascoli": "演習（sorry を自分で埋める）",
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


def write_pdf(document: str, destination: Path) -> None:
    """印刷用 HTML を独立した Chrome プロファイルで刷り、成功時だけ置換する。"""
    import subprocess
    import tempfile
    import os
    import signal
    import time
    chrome = find_chrome()
    if chrome is None:
        raise RuntimeError("PDF: Chrome が必要です（CHROME で実行ファイルを指定、HTML のみなら --no-pdf）")
    destination.parent.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory() as tmp:
        src = Path(tmp) / "all.html"
        output = Path(tmp) / "result.pdf"
        src.write_text(document, encoding="utf-8")
        cmd = [chrome, "--headless=new", "--disable-gpu", "--no-first-run", "--disable-extensions",
               "--disable-background-networking", f"--user-data-dir={Path(tmp) / 'profile'}",
               f"--print-to-pdf={output}", "--no-pdf-header-footer", src.as_uri()]
        log_path = Path(tmp) / "chrome.log"
        complete = False
        # Chrome helpers may retain stdout pipes after printing on macOS. Use a
        # file log, and close only our isolated process group after the complete
        # PDF trailer has been written. Never attach to the user's browser.
        with log_path.open("wb") as log:
            process = subprocess.Popen(cmd, stdout=log, stderr=log, start_new_session=True)
            try:
                deadline = time.monotonic() + 600
                while time.monotonic() < deadline:
                    if output.exists() and output.stat().st_size > 64:
                        with output.open("rb") as pdf:
                            header = pdf.read(5)
                            pdf.seek(-64, 2)
                            complete = header == b"%PDF-" and pdf.read().rstrip().endswith(b"%%EOF")
                    if complete or process.poll() is not None:
                        break
                    time.sleep(.2)
            finally:
                if process.poll() is None:
                    os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
        if not complete:
            raise RuntimeError(f"PDF: 生成に失敗（exit {process.returncode}）\n{log_path.read_text(errors='replace')}")
        # 同じファイルシステム内で原子的に置換し、失敗を古い PDF で隠さない。
        staged = destination.with_suffix(".pdf.tmp")
        staged.write_bytes(output.read_bytes())
        staged.replace(destination)
    print(f"  {destination.relative_to(ROOT)} 生成（{destination.stat().st_size / 1e6:.1f} MB）")


def build_pdf(titles: dict, bodies: dict) -> None:
    write_pdf(pdf_html(titles, bodies), PDF_OUT)

# ---------------------------------------------------------------- main

def build_inputs():
    paths = [*SRC.glob("*.lean"), *Path(__file__).parent.glob("*.py"),
             *(ROOT / "tools/slides").glob("*"), *(ROOT / "slides").glob("*.json"), ROOT / "lean-toolchain"]
    return sorted(path for path in paths if path.is_file())


def file_digest(path):
    import hashlib
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_signature(with_pdf):
    import hashlib
    return hashlib.sha256((str(with_pdf) + "\n" + "\n".join(
        str(path.relative_to(ROOT)) + ":" + file_digest(path) for path in build_inputs())).encode()).hexdigest()


def main(with_pdf: bool = True, with_slides: bool = True, if_needed: bool = False):
    import json
    cache = ROOT / ".lake/textbook-build.json"
    if if_needed and with_slides and cache.exists():
        try:
            previous = json.loads(cache.read_text())
            if previous["signature"] == build_signature(with_pdf) and previous["outputs"] and all(
                    (ROOT / name).is_file() and file_digest(ROOT / name) == value
                    for name, value in previous["outputs"].items()):
                print("  通読版・講義版の HTML/PDF は最新です。")
                return
        except (OSError, ValueError, KeyError):
            pass
    references = refs.analyze(SRC, CHAPTERS, SOL_FILES, parse)
    if references.errors:
        raise SystemExit("\n".join(references.errors))
    try:
        for path in references.write():
            print(f"  {path.name}: 節番号・参照を更新")
    except (OSError, ValueError) as exc:
        raise SystemExit(str(exc)) from exc
    # Snapshot after reference synchronization, before rendering. An edit made
    # during a long PDF export must invalidate the next build, not be cached.
    source_signature = build_signature(with_pdf) if with_slides and if_needed else None
    titles, bodies = {}, {}
    for name in CHAPTERS:
        segments = parse(SRC / f"{name}.lean")
        titles[name] = chapter_title(segments)
        bodies[name] = render_chapter(name, segments, references.sections)
    OUT.mkdir(exist_ok=True)
    (OUT / ".nojekyll").write_text("")
    for idx, name in enumerate(CHAPTERS):
        out_path = OUT / f"{name.lower()}.html"
        slide_link = f'<p class="lecture-link"><a href="slides/{name.lower()}.html">講義用スライド</a></p>' if with_slides else ""
        out_path.write_text(page(titles[name], slide_link + bodies[name], nav_html(idx)), encoding="utf-8")
        print(f"  {name}.lean → docs/{name.lower()}.html")

    # 受講者用の Lean ファイル（解説を省いた版）は、正本の src/ からだけ作る
    with_student = SRC == ROOT / "src"
    links = []
    if with_slides:
        links.append('<a href="slides/index.html">講義用スライド</a>')
    if with_student:
        links.append('<a href="student/index.html">受講者用の Lean ファイル</a>')
    (OUT / "index.html").write_text(
        page(SITE_TITLE, (f'<p>{"・".join(links)}</p>' if links else '') +
             toc_html(titles, lambda n: f"{n.lower()}.html")), encoding="utf-8")
    print("  index.html 生成")
    if with_student:
        import student
        student.main(docs=OUT / "student", titles=titles)

    if with_slides:
        import slides
        slide_document, _ = slides.build(titles, bodies, CHAPTERS, OUT, head=KATEX_HEAD)
    if with_pdf:
        build_pdf(titles, bodies)
        if with_slides:
            write_pdf(slide_document, PDF_OUT.with_name("slides.pdf"))
    if with_slides and if_needed:
        outputs = [OUT / "index.html", OUT / "slides/index.html"]
        outputs += [OUT / f"{name.lower()}.html" for name in CHAPTERS]
        outputs += [OUT / f"slides/{name.lower()}.html" for name in CHAPTERS]
        if with_pdf:
            outputs += [PDF_OUT, PDF_OUT.with_name("slides.pdf")]
        cache.parent.mkdir(exist_ok=True)
        cache.write_text(json.dumps({"signature": source_signature, "outputs": {
            str(path.relative_to(ROOT)): file_digest(path) for path in outputs}}, indent=2) + "\n")


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser(description="src/*.lean → 通読版・講義版の HTML と PDF")
    ap.add_argument("--no-pdf", action="store_true", help="2種類の PDF を省略し、2種類の HTML だけ生成する")
    ap.add_argument("--if-needed", action="store_true", help="入力と生成物が一致していれば再生成を省略する")
    args = ap.parse_args()
    main(with_pdf=not args.no_pdf, if_needed=args.if_needed)
