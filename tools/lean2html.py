#!/usr/bin/env python3
"""Top/*.lean から講義用 HTML を生成する（依存なし・Python 標準ライブラリのみ）。

使い方:
    python3 tools/lean2html.py

変換規則:
  * `/-! ... -/` ブロック → 地の文（この教材で使う Markdown サブセットを HTML 化）
  * それ以外（宣言・docstring・コメント・#check）→ コードブロック（簡易ハイライト付き）

章構成を変えるときは CHAPTERS を書き換えるだけでよい。
"""

import html
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "Top"
OUT = ROOT / "docs"

# 章構成（表示順）。ExtraSol（解答）は公開しない。
CHAPTERS = ["Intro", "CH", "Top", "Extra"]

SITE_TITLE = "Lean 4 で書く位相空間 — ミニ教材"
SITE_NOTE = (
    "数学的概念やその証明をプログラムとして書くとはどういうことか、"
    "なぜそれで証明の正しさを検証したと思えるのか、を実感するための教材。"
    "読む順は Intro → CH → Top（→ 演習 Extra）。"
    "ソースは <a href=\"https://github.com/unaoya/lean-intro\">GitHub</a> の "
    "<code>Top/*.lean</code>（このページはそこから自動生成）。"
)

# ---------------------------------------------------------------- inline md

def inline(text: str) -> str:
    """インライン要素: `code` と **bold**。コード内は bold 処理しない。"""
    parts = re.split(r"(`[^`]*`)", text)
    out = []
    for p in parts:
        if p.startswith("`") and p.endswith("`") and len(p) >= 2:
            out.append("<code>" + html.escape(p[1:-1]) + "</code>")
        else:
            e = html.escape(p)
            e = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", e)
            out.append(e)
    return "".join(out)

# ---------------------------------------------------------------- prose (md subset)

def smart_join(parts: list[str]) -> str:
    """日本語の折返しは区切りなしで連結するが、行境界のどちらかが
    英数字やコード（バッククォート）のときは空白を1つ入れる。"""
    out = parts[0] if parts else ""
    for nxt in parts[1:]:
        if out and nxt and (re.match(r"[A-Za-z0-9`*]", out[-1]) or re.match(r"[A-Za-z0-9`*]", nxt[0])):
            out += " " + nxt
        else:
            out += nxt
    return out


def render_prose(lines: list[str]) -> str:
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
            out.append(f"<h{level}>{inline(m.group(2))}</h{level}>")
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
                out.append("<thead><tr>" + "".join(f"<th>{inline(c)}</th>" for c in rows[0]) + "</tr></thead>")
                body = rows[2:]
            else:
                body = rows
            out.append("<tbody>")
            for r in body:
                out.append("<tr>" + "".join(f"<td>{inline(c)}</td>" for c in r) + "</tr>")
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
            out.append('<pre class="quote"><code>' + html.escape("\n".join(code)) + "</code></pre>")
            continue
        # リスト（* / 1. 、2字下げで入れ子と継続行）
        if re.match(r"^ *(\*|\d+\.) ", line):
            i, block = render_list(lines, i)
            out.append(block)
            continue
        # 段落（日本語の折返しなので区切りなしで連結）
        para = []
        while i < n and lines[i].strip() != "" and not re.match(r"^(#{1,4} |\||    | *(\*|\d+\.) )", lines[i]):
            para.append(lines[i].strip())
            i += 1
        out.append(f"<p>{inline(smart_join(para))}</p>")
    return "\n".join(out)


def render_list(lines: list[str], i: int) -> tuple[int, str]:
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
            out.append("<li>" + inline(smart_join(texts)) + "</li>")
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
KW_RE = re.compile(r"(?<![\w_.'])(" + KEYWORDS + r")(?![\w_'])")
SORT_RE = re.compile(r"(?<![\w_.'])(Type|Prop|Sort)(?![\w_'])")
CMD_RE = re.compile(r"(#check|#print|#eval|#guard)")


def hl_code_part(code: str) -> str:
    """コード片（コメント以外）のハイライト。エスケープしてから span を差す。"""
    e = html.escape(code)
    e = CMD_RE.sub(r'<span class="kw">\1</span>', e)
    e = KW_RE.sub(lambda m: f'<span class="kw">{m.group(1)}</span>'
                  if m.group(1) != "sorry" else '<span class="sorry">sorry</span>', e)
    e = SORT_RE.sub(r'<span class="sort">\1</span>', e)
    return e


def render_code(lines: list[str]) -> str:
    out = []
    in_doc = False
    for line in lines:
        if in_doc:
            out.append(f'<span class="doc">{html.escape(line)}</span>')
            if "-/" in line:
                in_doc = False
            continue
        if line.lstrip().startswith("/--"):
            out.append(f'<span class="doc">{html.escape(line)}</span>')
            if "-/" not in line:
                in_doc = True
            continue
        idx = line.find("--")
        if idx >= 0:
            code, comment = line[:idx], line[idx:]
            out.append(hl_code_part(code) + f'<span class="cm">{html.escape(comment)}</span>')
        else:
            out.append(hl_code_part(line))
    return '<pre class="lean"><code>' + "\n".join(out) + "</code></pre>"

# ---------------------------------------------------------------- file parsing

def parse(path: Path) -> list[tuple[str, list[str]]]:
    """ファイルを (kind, lines) のセグメント列に分ける。kind は 'prose' か 'code'。"""
    lines = path.read_text(encoding="utf-8").split("\n")
    segments = []
    cur_kind, cur = None, []

    def flush():
        nonlocal cur_kind, cur
        if cur_kind == "code":
            while cur and cur[0].strip() == "":
                cur.pop(0)
            while cur and cur[-1].strip() == "":
                cur.pop()
        if cur_kind and cur:
            segments.append((cur_kind, cur))
        cur_kind, cur = None, []

    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("/-!"):
            flush()
            body = [line[3:].lstrip()]
            while "-/" not in body[-1] and i + 1 < len(lines):
                i += 1
                body.append(lines[i])
            # 閉じ `-/` を除去（行末どちらのスタイルにも対応）
            body[-1] = body[-1][: body[-1].rfind("-/")].rstrip()
            cur_kind, cur = "prose", [b for b in body]
            flush()
        else:
            if cur_kind != "code":
                flush()
                cur_kind = "code"
            cur.append(line)
        i += 1
    flush()
    return segments


def chapter_title(segments) -> str:
    for kind, lines in segments:
        if kind == "prose":
            for l in lines:
                m = re.match(r"^# (.*)$", l)
                if m:
                    return m.group(1)
    return "無題"

# ---------------------------------------------------------------- page template

CSS = """
:root { --fg: #1a1a1a; --bg: #ffffff; --code-bg: #f5f5f0; --border: #ddd;
        --kw: #7b2d8b; --doc: #1a7f37; --cm: #8a8a8a; --sort: #0550ae; --sorry: #c0392b;
        --link: #0969da; --quote-bg: #f0f4f8; }
@media (prefers-color-scheme: dark) {
  :root { --fg: #d8d8d3; --bg: #1e1e1e; --code-bg: #262626; --border: #444;
          --kw: #d38ae0; --doc: #7ec699; --cm: #888; --sort: #6cb6ff; --sorry: #e07a6a;
          --link: #58a6ff; --quote-bg: #24292e; }
}
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
"""


def nav_html(idx: int) -> str:
    prev_a = ""
    next_a = ""
    if idx > 0:
        prev_a = f'<a href="{CHAPTERS[idx-1].lower()}.html">← {CHAPTERS[idx-1]}</a>'
    if idx + 1 < len(CHAPTERS):
        next_a = f'<a href="{CHAPTERS[idx+1].lower()}.html">{CHAPTERS[idx+1]} →</a>'
    return f'<nav><span>{prev_a}</span><a href="index.html">目次</a><span>{next_a}</span></nav>'


def page(title: str, body: str, nav: str = "") -> str:
    return f"""<!DOCTYPE html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)}</title>
<style>{CSS}</style>
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

# ---------------------------------------------------------------- main

def main():
    OUT.mkdir(exist_ok=True)
    (OUT / ".nojekyll").write_text("")
    titles = {}
    for idx, name in enumerate(CHAPTERS):
        segments = parse(SRC / f"{name}.lean")
        titles[name] = chapter_title(segments)
        body = []
        for kind, lines in segments:
            body.append(render_prose(lines) if kind == "prose" else render_code(lines))
        out_path = OUT / f"{name.lower()}.html"
        out_path.write_text(page(titles[name], "\n".join(body), nav_html(idx)), encoding="utf-8")
        print(f"  {name}.lean → docs/{name.lower()}.html")

    toc = [f"<h1>{html.escape(SITE_TITLE)}</h1>", f"<p>{SITE_NOTE}</p>", "<ol>"]
    for name in CHAPTERS:
        label = "（演習）" if name == "Extra" else ""
        toc.append(f'<li><a href="{name.lower()}.html">{inline(titles[name])}</a>{label}</li>')
    toc.append("</ol>")
    (OUT / "index.html").write_text(page(SITE_TITLE, "\n".join(toc)), encoding="utf-8")
    print("  index.html 生成")


if __name__ == "__main__":
    main()
