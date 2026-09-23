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
ANSWER_HEADING_HEIGHT = 44
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
    layout: str = "normal"
    continuation: bool = False
    source_text: str = ""
    answer: bool = False
    reveal_items: bool = False
    automatic: bool = True
    join_key: str = ""


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
                if node.tag in {"h1", "h2"} or node.attrs.get("id", "").startswith("sec-"):
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
    valid = {"section", "heading", "tag", "class", "text", "starts", "code", "declaration", "kind"}
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
        if key == "class" and value not in block.node.attrs.get("class", "").split():
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
        if set(rule) - {"at", "break", "id", "label", "layout", "reveal"}:
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
        layout = rule.get("layout", "")
        if "layout" in rule and (layout not in {"normal", "compact"} or action != "page"):
            raise ValueError(f"{chapter}: layout must be normal or compact on a page boundary: {rule}")
        block.layout = layout
        if "reveal" in rule:
            if rule["reveal"] != "items" or block.node.tag not in {"ol", "ul"}:
                raise ValueError(f"{chapter}: reveal must be items on a list: {rule}")
            block.reveal_items = True


def columns(text):
    return sum(2 if unicodedata.east_asian_width(char) in "WF" else 1 for char in text)


def height_limit(layout):
    # Compact screens can use the space down to the footer (top 100, footer 657).
    return 540 if layout == "compact" else MAX_HEIGHT


def estimate(node, layout="normal"):
    """Conservative 1280 x 720 projection geometry; never shrink type to fit."""
    if node.tag == "details":
        return 48
    if "answer-heading" in node.attrs.get("class", "").split():
        return ANSWER_HEADING_HEIGHT
    if node.tag.startswith("h") and node.tag in {"h1", "h2", "h3", "h4"}:
        if layout == "compact" and node.tag in {"h3", "h4"}:
            return 25 + 46 * max(1, math.ceil(columns(node.text) / 72))
        return 40 + 55 * max(1, math.ceil(columns(node.text) / 64))
    if node.tag == "pre":
        return (32 if layout == "compact" else 60) + sum(max(1, math.ceil(columns(line) / 60)) * (40 if layout == "compact" else 46)
                        for line in node.text.rstrip("\n").split("\n"))
    if node.tag in {"ul", "ol"}:
        margin = 0 if "list-fragment" in node.attrs.get("class", "").split() else 12
        return sum(estimate(item, layout) for item in node.children if isinstance(item, Node)) + margin
    if node.tag == "table":
        return sum(estimate(row) for group in node.children if isinstance(group, Node)
                   for row in (group.children if group.tag in {"thead", "tbody"} else [group]) if isinstance(row, Node)) + 20
    if node.tag == "tr":
        cells = [cell for cell in node.children if isinstance(cell, Node)]
        return 18 + max((math.ceil(columns(cell.text) / max(8, 66 / len(cells))) for cell in cells), default=1) * 40
    margin = 18 if layout == "compact" and node.tag == "p" else 28
    return margin + max(1, math.ceil(columns(node.text) / (64 if node.tag == "li" else 72))) * 49


def split_block(block, max_height=None):
    if max_height is None:
        max_height = height_limit(block.layout)
    node = block.node
    if estimate(node, block.layout) <= max_height or node.tag == "details":
        return [block]
    pieces = []
    if node.tag in {"ol", "ul"}:
        number = int(node.attrs.get("start", 1))
        for item in node.children:
            if not isinstance(item, Node):
                continue
            for part in split_block(replace(block, node=item, source_text=item.text), max_height - 12):
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
                if estimate(node.slice(start, candidate), block.layout) > max_height - 20:
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
        if estimate(piece, block.layout) > max_height:
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
    layout: str = "normal"
    column_at: str = ""
    editorial: bool = False

    @property
    def height(self):
        return sum(estimate(block.node, self.layout) for step in self.steps for block in step)


def is_exercise_heading(block):
    return block.node.tag in {"h3", "h4"} and "✏ 練習" in block.node.text


def is_heading(block):
    return block.node.tag in {"h1", "h2", "h3", "h4"}


def presentation_blocks(blocks):
    """Use a compact, progressive flow outside explicitly authored page groups."""
    automatic, layout, previous = True, "compact", None
    for block in blocks:
        if (previous is None or (block.section, block.kind) != (previous.section, previous.kind) or
                (is_heading(block) and block.action == "auto")):
            automatic, layout = True, "compact"
        if block.action == "page":
            automatic, layout = not block.layout, block.layout or "compact"
        reveal = block.reveal_items or (automatic and block.action == "auto" and
                                        block.node.tag in {"ol", "ul"} and
                                        "data-exercise" not in block.node.attrs)
        yield replace(block, automatic=automatic, layout=layout, reveal_items=reveal)
        previous = block


def automatic_step(block, previous, preceding=None):
    if not block.automatic or block.action != "auto" or block.answer or not previous:
        return False
    if is_heading(previous) or "data-exercise" in block.node.attrs:
        return False
    # An introductory sentence and its example form one reveal. The result's
    # interpretation appears together with the result, ready to explain aloud.
    if block.node.tag == "pre" and previous.node.tag == "p" and previous.node.text.rstrip().endswith((":", "：")):
        return False
    if (block.node.tag == "p" and previous.node.tag == "pre" and
            "quote" in previous.node.attrs.get("class", "").split() and preceding and
            preceding.node.tag == "pre" and "lean" in preceding.node.attrs.get("class", "").split()):
        return False
    return True


def exercise_blocks(blocks):
    """Reveal each answer after its own question, using the same flow in HTML/PDF."""
    for block in blocks:
        number = block.node.attrs.get("data-exercise")
        if is_exercise_heading(block):
            yield replace(block, layout="compact")
        elif not number:
            yield block
        elif block.node.tag == "ol":
            yield replace(block, action="page" if block.action == "auto" else block.action,
                          layout="compact", label=block.label or f"練習 {number}")
        elif block.node.tag == "details":
            for child in block.node.children:
                if not isinstance(child, Node):
                    continue
                summary = child.tag == "summary"
                if summary:
                    child = Node("p", {"class": "answer-heading"}, child.children)
                yield replace(block, node=child, source_text=child.text, answer=True,
                              key=digest(block.key + child.render()), action="step" if summary else "keep",
                              layout="compact", label=f"練習 {number}・解答")
        else:
            yield block


def reveal_blocks(blocks):
    for block in exercise_blocks(presentation_blocks(blocks)):
        if not block.reveal_items:
            yield block
            continue
        number = int(block.node.attrs.get("start", 1))
        items = [child for child in block.node.children if isinstance(child, Node)]
        for index, item in enumerate(items):
            attrs = dict(block.node.attrs)
            attrs["class"] = (attrs.get("class", "") + " list-fragment").strip()
            if block.node.tag == "ol":
                attrs["start"] = str(number + index)
            if index:
                attrs.pop("id", None)
            node = Node(block.node.tag, attrs, [item])
            yield replace(block, node=node, key=block.key + "-" + digest(str(index) + item.render()),
                          action=block.action if index == 0 else "step",
                          page_id=block.page_id if index == 0 else "", source_text=item.text,
                          reveal_items=False)


def paginate(blocks, chapter):
    pages = []
    current = None
    previous = None
    expanded = []
    prepared = list(reveal_blocks(blocks))
    for index, block in enumerate(prepared):
        budget = height_limit(block.layout)
        if block.answer:
            budget -= ANSWER_HEADING_HEIGHT
        elif index and (is_exercise_heading(prepared[index - 1]) or
                        (block.automatic and is_heading(prepared[index - 1]))):
            # Reserve room for a heading when splitting the first long block.
            budget = height_limit(block.layout) - estimate(prepared[index - 1].node, block.layout)
        expanded.extend(split_block(block, budget))

    def required_space(index, layout):
        block = expanded[index]
        height = estimate(block.node, layout)
        if index + 1 == len(expanded):
            return height
        following = expanded[index + 1]
        same_group = (block.section, block.kind, block.answer) == (following.section, following.kind, following.answer)
        if "answer-heading" in block.node.attrs.get("class", "").split():
            return height + required_space(index + 1, layout)
        # Keep short commands and results together, including in the main text.
        if ((block.answer or block.automatic) and same_group and following.action != "page" and
                block.node.tag == "pre" and "lean" in block.node.attrs.get("class", "")):
            if following.node.tag == "pre" and "quote" in following.node.attrs.get("class", ""):
                paired = height + estimate(following.node, layout)
                budget = height_limit(layout) - (ANSWER_HEADING_HEIGHT if block.answer else 0)
                if paired <= budget:
                    height = paired
                    if index + 2 < len(expanded):
                        explanation = expanded[index + 2]
                        combined = paired + estimate(explanation.node, layout)
                        if (explanation.answer == block.answer and explanation.section == block.section and
                                explanation.kind == block.kind and explanation.action != "page" and
                                explanation.node.tag == "p" and combined <= budget):
                            height = combined
        if (block.automatic and not block.answer and same_group and following.action != "page" and
                (is_heading(block) or (block.node.tag == "p" and following.node.tag == "pre" and
                                      block.node.text.rstrip().endswith((":", "："))))):
            combined = height + required_space(index + 1, layout)
            if combined <= height_limit(layout):
                height = combined
        return height

    for index, block in enumerate(expanded):
        if block.node.tag == "details":
            if current is None:
                raise ValueError("Solution without preceding exercise")
            if current.height + 48 * (len(current.answers) + 1) > MAX_HEIGHT:
                current = Slide(f"{chapter.lower()}-answers-{block.key}", block.heading + "・解答",
                                block.section, block.kind)
                pages.append(current)
            current.answers.append(block)
            continue
        heading = is_heading(block)
        is_code = block.node.tag == "pre" and "lean" in block.node.attrs.get("class", "")
        current_has_code = current and any(b.node.tag == "pre" for step in current.steps for b in step)
        # Keep an answer label with the first part of its answer.
        required_height = required_space(index, current.layout if current else block.layout)
        exercise = block.node.tag == "ol" and "data-exercise" in block.node.attrs
        just_exercise_heading = current and all(
            is_exercise_heading(b)
            for step in current.steps for b in step) and any(current.steps)
        if exercise and just_exercise_heading and current.height + required_height <= height_limit(block.layout):
            current.layout, current.label = block.layout, block.label
        new = (current is None or (block.action == "page" and not (exercise and just_exercise_heading)) or
               current.kind != block.kind or current.section != block.section or
               current.height + required_height > height_limit(current.layout) or
               (previous is not None and previous.answer and not block.answer) or
               bool(current.answers) or
               (block.action not in {"keep", "step"} and
                (heading or (not block.automatic and is_code and current_has_code))))
        if new:
            label = block.label or (normalized(block.node.text)[:65] if heading else block.heading)
            if block.continuation:
                label += "（続き）"
            current = Slide(f"{chapter.lower()}-{block.page_id or block.key}", label, block.section, block.kind,
                            layout=block.layout)
            pages.append(current)
        elif block.action == "step" or automatic_step(block, previous, expanded[index - 2] if index > 1 else None) or (block.action != "keep" and block.node.tag == "pre" and
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


def chapter_label(chapter):
    if chapter == "Index":
        return "はじめに"
    numbered = re.fullmatch(r"([0-9]+)_.+", chapter)
    return f"第{int(numbered[1])}章" if numbered else chapter


def slide_articles(pages, *, print_steps=False, chapter=""):
    output = []
    for index, slide in enumerate(pages):
        stages = (range(1, len(slide.steps) + 1) if any(slide.steps) else []) if print_steps else [len(slide.steps)]
        for stage in stages:
            parts = []
            if slide.editorial:
                from editorial_slides import render_content
                parts.append(render_content(slide, stage if print_steps else None, reserve_space=print_steps))
            for number, step in enumerate([] if slide.editorial else slide.steps[:stage]):
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
            if slide.layout == "compact":
                attrs += ' data-layout="compact"'
            if slide.editorial:
                attrs += ' data-editorial="true"'
            if print_steps:
                if slide.editorial:
                    parts = [re.sub(r' id="[^"]+"', '', part) for part in parts]
                    parts = [re.sub(r'href="([^"]+)"', lambda m: 'href="' + urljoin(
                        'https://unaoya.github.io/lean-intro/' + chapter.lower() + '.html', m[1]) + '"', part) for part in parts]
                head = f'<header class="print-head">{html.escape(chapter_label(chapter))} <span>{html.escape(slide.label)}</span></header>'
                foot = f'<footer class="print-foot">{index + 1} / {len(pages)} <span>表示 {stage} / {len(slide.steps)}</span></footer>'
                output.append(f'<article class="print-slide"{attrs}>{head}<div class="print-content"><div class="print-body">' +
                              "\n".join(parts) + f'</div></div>{foot}</article>')
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
                      f'>{html.escape(chapter_label(name))}</option>' for name in chapters)
    content = slide_articles(pages)
    # Lecture -> ordinary edition references, preserving the existing stable labels.
    def textbook_href(href):
        if re.match(r'(?:[a-z][a-z0-9+.-]*:|/)', href, re.I):
            return href
        return '../' + (chapter.lower() + '.html' if href.startswith(('#', '?')) else '') + href
    def link(match):
        href = match[1]
        # Chapter links in the shared index lead directly into the slide edition.
        if href.startswith('slides/'):
            return f'href="{href.removeprefix("slides/")}"'
        return f'target="_blank" rel="noopener" href="{textbook_href(href)}"'
    content = re.sub(r'href="([^"]+)"', link, content)
    label = chapter_label(chapter)
    return (template.replace("@@TITLE@@", html.escape(title)).replace("@@CHAPTER@@", html.escape(label))
            .replace("@@NOTES_HIDDEN@@", "" if any(p.kind != "main" for p in pages) else " hidden")
            .replace("@@CHAPTER_OPTIONS@@", options).replace("@@STYLE@@", (ASSETS / "style.css").read_text()).replace("@@HEAD@@", EXTRA_HEAD)
            .replace("@@SLIDES@@", content).replace("@@SCRIPT@@", (ASSETS / "layout.js").read_text() + "\n" +
                                                    (ASSETS / "lecture.js").read_text()))


def print_html(all_pages, titles):
    style = (ASSETS / "style.css").read_text() + "\n" + (ASSETS / "print.css").read_text()
    body = "\n".join(slide_articles(pages, print_steps=True, chapter=name) for name, pages in all_pages.items())
    return '<!doctype html><html lang="ja"><meta charset="utf-8"><title>はじめての Lean · スライド</title>' + \
           f'<style>{style}</style>{EXTRA_HEAD}<body class="print-deck">{body}' + \
           '<script>' + (ASSETS / "layout.js").read_text() + '</script></body></html>'


def build(titles, bodies, chapters, out, head="", include_notes=False, index_body=None):
    global EXTRA_HEAD
    EXTRA_HEAD = head
    folder = out / "slides"
    folder.mkdir(exist_ok=True)
    authored_index = index_body is not None
    if index_body is None:
        index_body = '<h1>はじめての Lean</h1><ol>' + ''.join(
            f'<li><a href="slides/{name.lower()}.html">{html.escape(titles[name])}</a></li>'
            for name in chapters) + '</ol>'
    chapters = ['Index', *chapters]
    titles = {'Index': 'はじめての Lean', **titles}
    bodies = {'Index': index_body, **bodies}
    all_pages = {}
    for chapter in chapters:
        blocks = blocks_from_html(bodies[chapter], chapter)
        path = CONFIG / f"{chapter}.json"
        config = (json.loads(path.read_text()) if path.exists() and (chapter != 'Index' or authored_index)
                  else {"version": 1, "rules": []})
        if config.get("version") == 2:
            from editorial_slides import paginate as editorial_paginate
            pages = editorial_paginate(blocks, config, chapter, include_notes=include_notes)
        else:
            apply_rules(blocks, config, chapter)
            # Resolve selectors against the full source even when notes are omitted,
            # so edits to a note cannot silently invalidate its boundary rules.
            if not include_notes:
                blocks = [block for block in blocks if block.kind == "main"]
            pages = paginate(blocks, chapter)
        all_pages[chapter] = pages
        (folder / f"{chapter.lower()}.html").write_text(html_page(chapter, titles[chapter], pages, chapters))
        print(f"  slides/{chapter.lower()}.html: {len(pages)} 画面 / {sum(len(p.steps) for p in pages)} 表示段階")
    return print_html(all_pages, titles), all_pages
