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

# ROOT は開発用プロジェクト（dev/）、REPO はリポジトリ直下。公開ページ docs/ は直下に置く
# （GitHub Pages の公開元が main ブランチの /docs のため）。
ROOT = Path(__file__).resolve().parent.parent
REPO = ROOT.parent
SRC = ROOT / "src"
OUT = REPO / "docs"

# 章構成（表示順）。*Sol（解答）は単独ページとしては公開しない。
CHAPTERS = ["01_TypesAndTerms", "02_Forall", "03_InductiveTypes", "04_Exists", "05_MathematicalTools", "06_Topology", "07_Exercises", "08_Ascoli", "09_Covering"]

# 公開済み URL は本文のコピーではなく、新しい章への転送ページとして残す。
LEGACY_CHAPTERS = {
    "Intro1a": "01_TypesAndTerms", "CH1": "02_Forall",
    "Intro1b": "03_InductiveTypes", "CH2": "04_Exists",
    "Intro2": "05_MathematicalTools", "Top": "06_Topology",
    "Extra": "07_Exercises", "Ascoli": "08_Ascoli",
    # 2往復構成より前の旧版（1往復構成）の URL
    "Intro1": "01_TypesAndTerms", "CH": "02_Forall",
}

# 通読版には含めるが、講義スライド（HTML・PDF）は作らない章。
SLIDE_EXCLUDED_CHAPTERS = {"06_Topology", "07_Exercises", "08_Ascoli", "09_Covering"}

# ✏ 練習に折りたたみで埋め込む解答ファイル（`/-! SOL 固定ラベル:問題番号 -/` 区切り）。
# 問題と解答の数・節内の順序が合わなければ生成をエラーで止める。
SOL_FILES = {name: name + "Sol" for name in CHAPTERS if name not in ("07_Exercises", "08_Ascoli", "09_Covering")}

SITE_TITLE = "はじめての Lean"
SITE_CONCEPT = (
    "この教材の目的は、Lean のコードを<strong>書ける</strong>ようになることではなく、"
    "証明が検査される<strong>仕組みを納得する</strong>ことである。"
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
    "<p>この2つの目標に向けて、第1章・第3章で次の3段階を学ぶ。</p>"
    "<ul>"
    "<li><strong>型がどのように作られるか</strong>を知る。</li>"
    "<li>その型の<strong>項をどのように作り、使うか</strong>を知る。</li>"
    "<li>複雑な項についても、<strong>部分項から順に型を推測できる</strong>ようになる。</li>"
    "</ul>"
    "<p>第2章・第4章では、「<strong>命題は型であり、証明はその型の項である</strong>」"
    "という対応を学ぶ。これによって、目標1の「項の型を推測する」仕組みが、"
    "目標2の「証明を検証する」仕組みへ接続する。</p>"
    "<h2>仕組みのスローガン</h2>"
    "<p>納得したいことは、突き詰めれば次の2つである。</p>"
    "<ol>"
    "<li>文字列が<strong>項</strong>であるかどうか、つまり文法規則に従っているかは、"
    "機械的に判定できる。</li>"
    "<li>項が与えられたら、<strong>型</strong>が付くかどうかを機械的に判定でき、"
    "付く場合はその型を計算できる。</li>"
    "</ol>"
    "<h2>設計の方針</h2>"
    "<ul>"
    "<li><strong>タクティクについて詳しくは説明しない</strong>。第6章では、"
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
    "<ol>"
    "<li><strong>第1・2章 — 依存関数型から、ならば・全称の証明へ。</strong>"
    "第1章で項と型、定義、関数・依存関数、暗黙引数を学ぶ。"
    "続く第2章では、仮定や対象を受け取り、適用して進む証明を読む。"
    "「単射どうしの合成は単射」の証明まで進み、"
    "型検査が証明の検査になることを確かめる。</li>"
    "<li><strong>第3・4章 — 帰納型から、かつ・または・存在の証明へ。</strong>"
    "第3章で帰納型、場合分け・再帰、structure を学び、"
    "項を作る・分解する道具を増やす。続く第4章では、その道具を使って"
    "「かつ」「または」「矛盾」「存在」の証明を読む。"
    "偶数の和や全射の合成を例に、関数・構成子・場合分けを組み合わせ、"
    "等式の仕組みと証明検査の全体像を整理する。</li>"
    "</ol>"
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
            title = (f'{heading["number"]}. {heading["title"]}' if heading['marks'] == '##'
                     else heading['title']) if heading else m.group(2)
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


def exercise_parts(lines):
    """Split exercise prose without changing the local SOL lookup numbers."""
    if not any(EXERCISE_HEAD_RE.match(line) for line in lines):
        return [(None, lines)]
    starts = [(i, int(match[1])) for i, line in enumerate(lines)
              if (match := ITEM_RE.match(line))]
    if not starts:
        return [(None, lines)]
    return [(None, lines[:starts[0][0]])] + [
        (item, lines[start:starts[index + 1][0] if index + 1 < len(starts) else len(lines)])
        for index, (start, item) in enumerate(starts)]


def exercise_count(segments):
    return sum(item is not None for kind, lines in segments if kind == "prose"
               for item, _ in exercise_parts(lines))


def render_chapter(name: str, segments, sections=None, *, exercise_start=1) -> str:
    """本文をレンダリングする。長い注記は CALLOUT_START/END でコードごと囲む。"""
    sol_path = SRC / f"{SOL_FILES[name]}.lean" if name in SOL_FILES else None
    sols = parse_solutions(sol_path) if sol_path and sol_path.exists() else None
    queues = defaultdict(deque)
    for (label, item), solution in sols or []:
        queues[label].append((item, solution))
    body = []
    sec, sol_i = None, 0
    exercise_number = exercise_start
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
        parts = []
        for item, question_lines in exercise_parts(lines):
            rendered = render_prose(question_lines, name, sections)
            if item is None:
                parts.append(rendered)
                continue
            number = exercise_number
            exercise_number += 1
            rendered = rendered.replace('<ol>', f'<ol class="exercise" start="{number}" data-exercise="{number}">', 1)
            parts.append(rendered)
            if sols is None:
                continue
            label = f"{sec}:{item}"
            if not queues[sec]:
                raise SystemExit(f"error: {name} 練習 {label} の解答がない（{SOL_FILES[name]}.lean）")
            got, segs2 = queues[sec].popleft()
            sol_i += 1
            if got != item:
                raise SystemExit(f"error: {name} 練習 {label} の位置に SOL {got}（{SOL_FILES[name]}.lean の順序を確認）")
            inner = "\n".join(render_code(ls) if k == "code" else render_prose(ls, name, sections, section_ids=False) for k, ls in segs2)
            parts.append(f'<details class="sol" data-exercise="{number}"><summary>解答 {number}</summary>\n{inner}\n</details>')
        rendered = "\n".join(parts)
        callout = CALLOUT_HEAD_RE.match(first)
        if callout and active_callout is None:
            kind = "optional" if callout.group(1) == "補足" else "preview"
            rendered = f'<aside class="note note--{kind}">{rendered}</aside>'
        body.append(rendered)
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
ol[data-exercise] { padding-left: 2.8em; }
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
    "06_Topology": "定義から「コンパクト空間からハウスドルフ空間への連続全単射は同相写像である」の証明まで",
    "07_Exercises": "演習（sorry を自分で埋める）",
    "08_Ascoli": "演習（sorry を自分で埋める）",
    "09_Covering": "演習（sorry を自分で埋める）",
}


def introduction_html() -> str:
    """通読版と講義版で共有する、教材の目的・目標・構成。"""
    return f"<h1>{html.escape(SITE_TITLE)}</h1>\n<p>{SITE_CONCEPT}</p>\n{SITE_GOALS}"


def chapter_links_html(titles: dict, chapters, href, *, group_exercises=False) -> str:
    out = ["<ol>"]
    exercises_added = False
    for name in chapters:
        if group_exercises and name in {"07_Exercises", "08_Ascoli", "09_Covering"}:
            if not exercises_added:
                out.append(f'<li><a href="{href(name)}">発展演習</a></li>')
                exercises_added = True
            continue
        role = ROLES.get(name, "")
        suffix = f" — {role}" if role else ""
        out.append(f'<li><a href="{href(name)}">{inline(titles[name])}</a>{suffix}</li>')
    out.append("</ol>")
    return "\n".join(out)


def toc_html(titles: dict, href) -> str:
    """目次。`href(name)` は HTML の章ページ、または PDF 内のアンカー。"""
    return introduction_html() + f"\n<p>{SITE_NOTE}</p>\n" + chapter_links_html(titles, CHAPTERS, href)


def lecture_index_html(titles: dict, chapters) -> str:
    return (introduction_html() + '<h2>講義の各章</h2>' +
            chapter_links_html(titles, CHAPTERS,
                               lambda name: ('slides/' if name in chapters else '') + name.lower() + '.html',
                               group_exercises=True))


def legacy_redirect_html(old: str, new: str, *, slide=False) -> str:
    """Keep published links, including lecture page/reveal hashes, working."""
    import json
    destination = new.lower() + ".html"
    migrate_hash = (f'if (fragment.startsWith({json.dumps("#" + old.lower() + "-")})) '
                    f'fragment = {json.dumps("#" + new.lower() + "-")} + fragment.slice({len(old) + 2});'
                    if slide else "")
    return f'''<!doctype html>
<html lang="ja"><head><meta charset="utf-8">
<title>ページは移動しました</title>
<script>
let fragment = location.hash;
{migrate_hash}
location.replace({json.dumps(destination)} + location.search + fragment);
</script>
<meta http-equiv="refresh" content="0; url={destination}">
</head><body><p>この章は<a href="{destination}">こちら</a>に移動しました。</p></body></html>
'''


def write_legacy_redirects(out: Path, slide_chapters) -> list[Path]:
    paths = []
    for old, new in LEGACY_CHAPTERS.items():
        for folder, is_slide in [(out, False)] + ([(out / "slides", True)] if new in slide_chapters else []):
            path = folder / (old.lower() + ".html")
            path.write_text(legacy_redirect_html(old, new, slide=is_slide), encoding="utf-8")
            paths.append(path)
    return paths

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
        body = bodies[name].replace('<details class="sol"', '<details open class="sol"')
        # Stable labels are globally unique, including in the combined document.
        body = re.sub(r'href="(?:[a-z0-9_-]+\.html)?#(sec-[A-Za-z0-9_.-]+)"', r'href="#\1"', body)
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


def build_signature(with_pdf, include_slide_notes=False):
    import hashlib
    return hashlib.sha256((str((with_pdf, include_slide_notes)) + "\n" + "\n".join(
        str(path.relative_to(ROOT)) + ":" + file_digest(path) for path in build_inputs())).encode()).hexdigest()


def main(with_pdf: bool = True, with_slides: bool = True, if_needed: bool = False,
         include_slide_notes: bool = False):
    import json
    slide_chapters = [name for name in CHAPTERS if name not in SLIDE_EXCLUDED_CHAPTERS]
    cache = ROOT / ".lake/textbook-build.json"
    if if_needed and with_slides and cache.exists():
        try:
            previous = json.loads(cache.read_text())
            if previous["signature"] == build_signature(with_pdf, include_slide_notes) and previous["outputs"] and not any(
                    (OUT / "slides" / f"{name.lower()}.html").exists() for name in SLIDE_EXCLUDED_CHAPTERS) and all(
                    (REPO / name).is_file() and file_digest(REPO / name) == value
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
    source_signature = build_signature(with_pdf, include_slide_notes) if with_slides and if_needed else None
    titles, bodies = {}, {}
    exercise_start = 1
    for name in CHAPTERS:
        segments = parse(SRC / f"{name}.lean")
        titles[name] = chapter_title(segments)
        bodies[name] = render_chapter(name, segments, references.sections, exercise_start=exercise_start)
        exercise_start += exercise_count(segments)
    OUT.mkdir(exist_ok=True)
    (OUT / ".nojekyll").write_text("")
    for idx, name in enumerate(CHAPTERS):
        out_path = OUT / f"{name.lower()}.html"
        slide_link = f'<p class="lecture-link"><a href="slides/{name.lower()}.html">講義用スライド</a></p>' if with_slides and name in slide_chapters else ""
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
        slide_document, _ = slides.build(titles, bodies, slide_chapters, OUT, head=KATEX_HEAD,
                                        include_notes=include_slide_notes,
                                        index_body=lecture_index_html(titles, slide_chapters))
        for name in SLIDE_EXCLUDED_CHAPTERS:
            (OUT / "slides" / f"{name.lower()}.html").unlink(missing_ok=True)
    redirects = write_legacy_redirects(OUT, slide_chapters if with_slides else []) if with_student else []
    if with_pdf:
        build_pdf(titles, bodies)
        if with_slides:
            write_pdf(slide_document, PDF_OUT.with_name("slides.pdf"))
    if with_slides and if_needed:
        outputs = [OUT / "index.html", OUT / "slides/index.html"]
        outputs += [OUT / f"{name.lower()}.html" for name in CHAPTERS]
        outputs += [OUT / f"slides/{name.lower()}.html" for name in slide_chapters]
        outputs += redirects
        if with_pdf:
            outputs += [PDF_OUT, PDF_OUT.with_name("slides.pdf")]
        cache.parent.mkdir(exist_ok=True)
        cache.write_text(json.dumps({"signature": source_signature, "outputs": {
            str(path.relative_to(REPO)): file_digest(path) for path in outputs}}, indent=2) + "\n")


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser(description="src/*.lean → 通読版・講義版の HTML と PDF")
    ap.add_argument("--no-pdf", action="store_true", help="2種類の PDF を省略し、2種類の HTML だけ生成する")
    ap.add_argument("--if-needed", action="store_true", help="入力と生成物が一致していれば再生成を省略する")
    ap.add_argument("--include-slide-notes", action="store_true", help="スライドの HTML・PDF に補足・先取りを含める（標準では省略）")
    args = ap.parse_args()
    main(with_pdf=not args.no_pdf, if_needed=args.if_needed, include_slide_notes=args.include_slide_notes)
