"""Shared textbook HTML -> lecture screens, with semantic boundary selectors.

Uses only Python's standard library. The ordinary and lecture editions consume
the exact same rendered chapter bodies, including solutions and optional notes.
"""
from dataclasses import dataclass, field, replace
import hashlib
import html
from html.parser import HTMLParser
import json
import math
from pathlib import Path
import re
import unicodedata
from urllib.parse import urljoin

ROOT = Path(__file__).resolve().parent.parent
ASSETS = ROOT / "tools/slides"
CONFIG = ROOT / "slides"
MAX_HEIGHT = 450
# 通読版と同じ追加の <head> 要素（数式を描画する KaTeX の読み込みなど）。build() で受け取る。
EXTRA_HEAD = ""
VOID = {"br", "hr", "img", "input", "meta", "link", "wbr"}


def normalized(text):
    return " ".join(text.split())


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()[:12]


@dataclass
class Node:
    tag: str
    attrs: dict = field(default_factory=dict)
    children: list = field(default_factory=list)

    @property
    def text(self):
        return "".join(child.text if isinstance(child, Node) else child for child in self.children)

    def render(self):
        inside = "".join(child.render() if isinstance(child, Node) else html.escape(child)
                         for child in self.children)
        if self.tag == "root":
            return inside
        attrs = "".join(f' {key}="{html.escape(value, quote=True)}"' if value is not None else f" {key}"
                        for key, value in self.attrs.items())
        return f"<{self.tag}{attrs}>" + ("" if self.tag in VOID else inside + f"</{self.tag}>")

    def slice(self, start, end):
        """Slice visible text while retaining inline markup, code spans and spaces."""
        result = Node(self.tag, dict(self.attrs))
        if start:
            result.attrs.pop("id", None)
        offset = 0
        for child in self.children:
            size = len(child.text if isinstance(child, Node) else child)
            left, right = max(0, start - offset), min(size, end - offset)
            if left < right:
                result.children.append(child.slice(left, right) if isinstance(child, Node) else child[left:right])
            offset += size
        return result


class FragmentParser(HTMLParser):
    def __init__(self, source):
        super().__init__(convert_charrefs=True)
        self.root = Node("root")
        self.stack = [self.root]
        self.feed(source)
        self.close()
        if len(self.stack) != 1:
            raise ValueError("Unclosed HTML in chapter")

    def handle_starttag(self, tag, attrs):
        node = Node(tag, dict(attrs))
        self.stack[-1].children.append(node)
        if tag not in VOID:
            self.stack.append(node)

    def handle_endtag(self, tag):
        if len(self.stack) == 1 or self.stack[-1].tag != tag:
            raise ValueError(f"Unbalanced HTML: {tag}")
        self.stack.pop()

    def handle_data(self, text):
        self.stack[-1].children.append(text)


@dataclass
class Block:
    node: Node
    section: str
    heading: str
    kind: str = "main"
    key: str = ""
    action: str = "auto"
    page_id: str = ""
    label: str = ""
    continuation: bool = False
    source_text: str = ""


def blocks_from_html(body, chapter):
    tree = FragmentParser(body).root
    blocks = []
    section, heading = f"{chapter}.intro", chapter
    used = set()

    def walk(nodes, kind="main"):
        nonlocal section, heading
        for node in nodes:
            if not isinstance(node, Node):
                if node.strip():
                    raise ValueError("Text outside chapter elements")
                continue
            if node.tag == "aside":
                note_kind = "preview" if "note--preview" in node.attrs.get("class", "") else "optional"
                saved_heading = heading
                walk(node.children, note_kind)
                heading = saved_heading
                continue
            if re.fullmatch(r"h[1-4]", node.tag):
                heading = normalized(node.text)
                if node.tag in {"h1", "h2"}:
                    section = node.attrs.get("id", "").removeprefix("sec-") or f"{chapter}.heading-{digest(heading)}"
                    if node.tag == "h1":
                        section = f"{chapter}.intro"
            key = digest(section + "|" + heading + "|" + node.tag + "|" + normalized(node.text))
            if key in used:
                key = digest(key + (blocks[-1].key if blocks else chapter))
            if key in used:
                raise ValueError("Cannot distinguish duplicate block identities")
            used.add(key)
            blocks.append(Block(node, section, heading, kind, key, source_text=node.text))

    walk(tree.children)
    expected = normalized(tree.text)
    actual = normalized(" ".join(block.source_text for block in blocks))
    if re.sub(r"\s", "", expected) != re.sub(r"\s", "", actual):
        raise ValueError(f"{chapter}: chapter text lost during extraction")
    return blocks


def matches(block, selector):
    valid = {"section", "heading", "tag", "text", "starts", "code", "declaration", "kind"}
    if not selector or set(selector) - valid:
        raise ValueError(f"Invalid semantic selector: {selector}")
    text = normalized(block.node.text)
    for key, value in selector.items():
        if key == "section" and block.section != value:
            return False
        if key == "heading" and not (block.node.tag.startswith("h") and text == normalized(value)):
            return False
        if key == "tag" and block.node.tag != value:
            return False
        if key == "kind" and block.kind != value:
            return False
        if key == "text" and text != normalized(value):
            return False
        if key == "starts" and not text.startswith(normalized(value)):
            return False
        if key == "code" and not (block.node.tag == "pre" and "lean" in block.node.attrs.get("class", "") and
                                    value.strip() in [line.strip() for line in block.node.text.splitlines()]):
            return False
        if key == "declaration" and not (block.node.tag == "pre" and "lean" in block.node.attrs.get("class", "") and re.search(
                r"(?m)^(?:noncomputable\s+)?(?:def|theorem|lemma|class|structure|inductive)\s+" +
                re.escape(value) + r"(?=\s|[:({\[])" , block.node.text)):
            return False
    return True


def apply_rules(blocks, config, chapter):
    if set(config) - {"version", "rules"} or config.get("version") != 1:
        raise ValueError(f"{chapter}: unsupported slide config")
    ids, selected = set(), set()
    for rule in config.get("rules", []):
        if set(rule) - {"at", "break", "id", "label"}:
            raise ValueError(f"{chapter}: unknown rule keys: {rule}")
        found = [block for block in blocks if matches(block, rule["at"])]
        if len(found) != 1:
            raise ValueError(f"{chapter}: selector must match exactly once, found {len(found)}: {rule['at']}")
        block = found[0]
        if block.key in selected:
            raise ValueError(f"{chapter}: conflicting rules: {rule['at']}")
        selected.add(block.key)
        action = rule.get("break", "page")
        if action not in {"page", "step", "keep"}:
            raise ValueError(f"{chapter}: invalid break: {action}")
        page_id = rule.get("id", "")
        if page_id and (not re.fullmatch(r"[a-z][a-z0-9-]*", page_id) or page_id in ids or action != "page"):
            raise ValueError(f"{chapter}: invalid or duplicate page id: {page_id}")
        ids.add(page_id)
        block.action, block.page_id, block.label = action, page_id, rule.get("label", "")


def columns(text):
    return sum(2 if unicodedata.east_asian_width(char) in "WF" else 1 for char in text)


def estimate(node):
    """Conservative 1280 x 720 projection geometry; never shrink type to fit."""
    if node.tag == "details":
        return 48
    if node.tag.startswith("h") and node.tag in {"h1", "h2", "h3", "h4"}:
        return 40 + 55 * max(1, math.ceil(columns(node.text) / 64))
    if node.tag == "pre":
        return 60 + sum(max(1, math.ceil(columns(line) / 60)) * 46
                        for line in node.text.rstrip("\n").split("\n"))
    if node.tag in {"ul", "ol"}:
        return sum(estimate(item) for item in node.children if isinstance(item, Node)) + 12
    if node.tag == "table":
        return sum(estimate(row) for group in node.children if isinstance(group, Node)
                   for row in (group.children if group.tag in {"thead", "tbody"} else [group]) if isinstance(row, Node)) + 20
    if node.tag == "tr":
        cells = [cell for cell in node.children if isinstance(cell, Node)]
        return 18 + max((math.ceil(columns(cell.text) / max(8, 66 / len(cells))) for cell in cells), default=1) * 40
    return 28 + max(1, math.ceil(columns(node.text) / (64 if node.tag == "li" else 72))) * 49


def split_block(block):
    node = block.node
    if estimate(node) <= MAX_HEIGHT or node.tag == "details":
        return [block]
    pieces = []
    if node.tag in {"ol", "ul"}:
        number = int(node.attrs.get("start", 1))
        for item in node.children:
            if not isinstance(item, Node):
                continue
            for part in split_block(replace(block, node=item, source_text=item.text)):
                attrs = dict(node.attrs)
                if node.tag == "ol":
                    attrs["start"] = str(number)
                pieces.append((Node(node.tag, attrs, [part.node]), part.source_text))
            number += 1
    elif node.tag == "table":
        groups = [child for child in node.children if isinstance(child, Node)]
        head = next((child for child in groups if child.tag == "thead"), None)
        rows = [row for group in groups if group.tag != "thead"
                for row in (group.children if group.tag == "tbody" else [group]) if isinstance(row, Node)]
        for index, row in enumerate(rows):
            # Repeated column headings are intentionally not counted as new source text.
            children = ([head] if head else []) + [Node("tbody", children=[row])]
            pieces.append((Node("table", dict(node.attrs), children),
                           (head.text if head and index == 0 else "") + row.text))
    else:
        text = node.text
        start = 0
        while start < len(text):
            end = start
            for candidate in range(start + 1, len(text) + 1):
                if estimate(node.slice(start, candidate)) > MAX_HEIGHT - 20:
                    break
                end = candidate
            if end == start:
                raise ValueError(f"Cannot paginate {block.section}: {text[start:start+50]}")
            if end < len(text):
                if node.tag == "pre":
                    newline = text.rfind("\n", start, end)
                    if newline > start:
                        end = newline + 1
                else:
                    stops = [match.end() + start for match in re.finditer(r"[。！？]\s*", text[start:end])]
                    if stops and stops[-1] > start + (end - start) // 3:
                        end = stops[-1]
                    else:
                        space = text.rfind(" ", start, end)
                        if space > start + (end - start) // 2:
                            end = space + 1
            pieces.append((node.slice(start, end), text[start:end]))
            start = end
    result = []
    for index, (piece, payload) in enumerate(pieces):
        if estimate(piece) > MAX_HEIGHT:
            raise ValueError(f"Oversized slide block in {block.section}: {piece.text[:80]}")
        result.append(replace(block, node=piece, key=block.key + "-" + digest(payload),
                              action=block.action if index == 0 else "page",
                              page_id=block.page_id if index == 0 else "",
                              continuation=index > 0, source_text=payload))
    if re.sub(r"\s", "", "".join(p.source_text for p in result)) != re.sub(r"\s", "", block.source_text):
        raise ValueError(f"Text lost during pagination: {block.section}")
    return result


@dataclass
class Slide:
    id: str
    label: str
    section: str
    kind: str
    steps: list = field(default_factory=lambda: [[]])
    answers: list = field(default_factory=list)

    @property
    def height(self):
        return sum(estimate(block.node) for step in self.steps for block in step)


def paginate(blocks, chapter):
    pages = []
    current = None
    previous = None
    expanded = [piece for block in blocks for piece in split_block(block)]
    for block in expanded:
        if block.node.tag == "details":
            if current is None:
                raise ValueError("Solution without preceding exercise")
            if current.height + 48 * (len(current.answers) + 1) > MAX_HEIGHT:
                current = Slide(f"{chapter.lower()}-answers-{block.key}", block.heading + "・解答",
                                block.section, block.kind)
                pages.append(current)
            current.answers.append(block)
            continue
        is_heading = block.node.tag in {"h1", "h2", "h3", "h4"}
        is_code = block.node.tag == "pre" and "lean" in block.node.attrs.get("class", "")
        current_has_code = current and any(b.node.tag == "pre" for step in current.steps for b in step)
        new = (current is None or block.action == "page" or
               current.kind != block.kind or current.section != block.section or
               current.height + estimate(block.node) > MAX_HEIGHT or
               bool(current.answers) or
               (block.action != "keep" and (is_heading or (is_code and current_has_code))))
        if new:
            label = block.label or (normalized(block.node.text)[:65] if is_heading else block.heading)
            if block.continuation:
                label += "（続き）"
            current = Slide(f"{chapter.lower()}-{block.page_id or block.key}", label, block.section, block.kind)
            pages.append(current)
        elif block.action == "step" or (block.node.tag == "pre" and
                "quote" in block.node.attrs.get("class", "") and previous and
                previous.node.tag == "pre" and "lean" in previous.node.attrs.get("class", "")):
            current.steps.append([])
        current.steps[-1].append(block)
        previous = block
    seen = [b.key for page in pages for step in page.steps for b in step]
    expected = [b.key for b in expanded if b.node.tag != "details"]
    if seen != expected:
        raise ValueError(f"{chapter}: slide coverage/order mismatch")
    return pages


def slide_articles(pages, *, print_steps=False, chapter=""):
    output = []
    for index, slide in enumerate(pages):
        stages = (range(1, len(slide.steps) + 1) if any(slide.steps) else []) if print_steps else [len(slide.steps)]
        for stage in stages:
            parts = []
            for number, step in enumerate(slide.steps[:stage]):
                # Section anchors live in headings. Avoid duplicate anchor IDs on repeated PDF stages.
                content = "\n".join(block.node.render() for block in step)
                if print_steps:
                    content = re.sub(r' id="[^"]+"', '', content)
                    base_chapter = chapter.split(' · ')[0]
                    content = re.sub(r'href="([^"]+)"', lambda match: 'href="' + urljoin(
                        'https://unaoya.github.io/lean-intro/' + base_chapter.lower() + '.html', match[1]) + '"', content)
                parts.append(f'<div class="step" data-step="{number}">{content}</div>')
            if not print_steps:
                parts += [block.node.render() for block in slide.answers]
            attrs = (f' data-kind="{slide.kind}" data-label="{html.escape(slide.label, quote=True)}" '
                     f'data-section="{html.escape(slide.section, quote=True)}"')
            if print_steps:
                head = f'<header class="print-head">{html.escape(chapter)} <span>{html.escape(slide.label)}</span></header>'
                foot = f'<footer class="print-foot">{index + 1} / {len(pages)} <span>表示 {stage} / {len(slide.steps)}</span></footer>'
                output.append(f'<article class="print-slide"{attrs}>{head}<div class="print-content">' +
                              "\n".join(parts) + f'</div>{foot}</article>')
            else:
                output.append(f'<article class="slide" id="{slide.id}"{attrs}>' + "\n".join(parts) + '</article>')
        if print_steps:
            for answer in slide.answers:
                children = [child for child in answer.node.children if isinstance(child, Node)]
                answer_blocks = []
                for child in children:
                    if child.tag == "summary":
                        child = Node("h3", children=child.children)
                    answer_blocks.append(replace(answer, node=child, source_text=child.text,
                                                 key=digest(answer.key + child.render()), action="auto"))
                answer_pages = paginate(answer_blocks, chapter + "-answers")
                output.append(slide_articles(answer_pages, print_steps=True, chapter=chapter + " · 練習の解答"))
    return "\n".join(output)


def html_page(chapter, title, pages, chapters):
    template = (ASSETS / "template.html").read_text()
    options = "".join(f'<option value="{name.lower()}.html"' + (" selected" if name == chapter else "") +
                      f'>{html.escape(name)}</option>' for name in chapters)
    content = slide_articles(pages)
    # Lecture -> ordinary edition references, preserving the existing stable labels.
    def textbook_href(href):
        if re.match(r'(?:[a-z][a-z0-9+.-]*:|/)', href, re.I):
            return href
        return '../' + (chapter.lower() + '.html' if href.startswith(('#', '?')) else '') + href
    content = re.sub(r'href="([^"]+)"', lambda match: 'target="_blank" rel="noopener" href="' +
                     textbook_href(match[1]) + '"', content)
    return (template.replace("@@TITLE@@", html.escape(title)).replace("@@CHAPTER@@", html.escape(chapter))
            .replace("@@CHAPTER_OPTIONS@@", options).replace("@@STYLE@@", (ASSETS / "style.css").read_text()).replace("@@HEAD@@", EXTRA_HEAD)
            .replace("@@SLIDES@@", content).replace("@@SCRIPT@@", (ASSETS / "lecture.js").read_text()))


def print_html(all_pages, titles):
    style = (ASSETS / "style.css").read_text() + "\n" + (ASSETS / "print.css").read_text()
    body = "\n".join(slide_articles(pages, print_steps=True, chapter=name) for name, pages in all_pages.items())
    return '<!doctype html><html lang="ja"><meta charset="utf-8"><title>はじめての Lean · スライド</title>' + \
           f'<style>{style}</style>{EXTRA_HEAD}<body class="print-deck">{body}</body></html>'


def build(titles, bodies, chapters, out, head=""):
    global EXTRA_HEAD
    EXTRA_HEAD = head
    folder = out / "slides"
    folder.mkdir(exist_ok=True)
    all_pages = {}
    for chapter in chapters:
        blocks = blocks_from_html(bodies[chapter], chapter)
        path = CONFIG / f"{chapter}.json"
        config = json.loads(path.read_text()) if path.exists() else {"version": 1, "rules": []}
        apply_rules(blocks, config, chapter)
        pages = paginate(blocks, chapter)
        all_pages[chapter] = pages
        (folder / f"{chapter.lower()}.html").write_text(html_page(chapter, titles[chapter], pages, chapters))
        print(f"  slides/{chapter.lower()}.html: {len(pages)} 画面 / {sum(len(p.steps) for p in pages)} 表示段階")
    links = "".join(f'<li><a href="{name.lower()}.html">{html.escape(titles[name])}</a></li>' for name in chapters)
    (folder / "index.html").write_text('<!doctype html><html lang="ja"><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width, initial-scale=1"><title>はじめての Lean · 講義用</title>'
        '<style>body{font-family:sans-serif;max-width:50rem;margin:4rem auto;padding:0 1.5rem;line-height:2}'
        'a{color:#235965}li{margin:1rem 0}</style><h1>はじめての Lean · 講義用</h1>'
        '<p>左右キーで進行。コードの出力は次の操作で表示します。</p><ol>' + links +
        '</ol><p><a href="../index.html">通読版</a></p></html>')
    return print_html(all_pages, titles), all_pages
