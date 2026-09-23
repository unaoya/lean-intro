"""Content-authored pages. Boundaries are semantic anchors, never block ordinals.

Unlike the fallback paginator, this path never invents page breaks. The editor
chooses each page and each intra-paragraph/code cut; rendering preserves the
original paragraph, code box and list so revealing more text doesn't add gaps.
"""
from dataclasses import dataclass, replace
from itertools import groupby
import re

import slides as s


@dataclass
class Item:
    block: s.Block
    question: str = ""
    part: str = ""
    order: int = 0
    source: s.Block | None = None
    following: str = ""


def source_items(blocks):
    result, question = [], ""
    for order, block in enumerate(blocks):
        if block.node.tag == "ol" and "data-exercise" in block.node.attrs:
            question = s.normalized(block.node.text)
        elif s.is_heading(block):
            question = ""
        if block.node.tag == "details":
            for node in block.node.children:
                if not isinstance(node, s.Node):
                    continue
                if node.tag == "summary":
                    node = s.Node("p", {"class": "answer-heading"}, node.children)
                result.append(Item(replace(block, node=node, source_text=node.text, answer=True,
                                          key=s.digest(block.key + node.render())), question, order=order))
            question = ""
        else:
            result.append(Item(block, question if "data-exercise" in block.node.attrs else "", order=order))
    for current, following in zip(result, result[1:]):
        current.following = s.normalized(following.block.node.text)
    return result


def matches(item, selector):
    selector = dict(selector)
    if item.block.answer != selector.pop("answer", False):
        return False
    if not s.normalized(item.question).startswith(s.normalized(selector.pop("question", ""))):
        return False
    if item.part != selector.pop("part", ""):
        return False
    if not item.following.startswith(s.normalized(selector.pop("next", ""))):
        return False
    return s.matches(item.source or item.block, selector)


def locate(items, selector, chapter):
    found = [i for i, item in enumerate(items) if matches(item, selector)]
    if len(found) != 1:
        raise ValueError(f"{chapter}: editorial anchor must match once, found {len(found)}: {selector}")
    return found[0]


def split_items(items, config, chapter):
    cuts = {}
    for rule in config.get("splits", []):
        if set(rule) != {"at", "before"}:
            raise ValueError(f"{chapter}: invalid split: {rule}")
        index = locate(items, rule["at"], chapter)
        if index in cuts:
            raise ValueError(f"{chapter}: repeated split anchor: {rule['at']}")
        text = items[index].block.node.text
        positions = []
        for anchor in rule["before"]:
            if not anchor or text.count(anchor) != 1:
                raise ValueError(f"{chapter}: split text must occur once: {anchor!r}")
            positions.append(text.index(anchor))
        if positions != sorted(set(positions)) or any(p == 0 for p in positions):
            raise ValueError(f"{chapter}: split anchors must follow source order")
        cuts[index] = (positions, rule["before"])
    result = []
    for index, item in enumerate(items):
        block = item.block
        positions, anchors = cuts.get(index, ([], []))
        boundaries = [0, *positions, len(block.node.text)]
        for part, (start, end) in enumerate(zip(boundaries, boundaries[1:])):
            node = block.node.slice(start, end) if positions else block.node
            result.append(replace(item, source=block, block=replace(block, node=node, source_text=node.text,
                                  key=block.key if not part else s.digest(block.key + anchors[part - 1]),
                                  join_key=block.key), part="" if not part else anchors[part - 1]))
    return result


def page_steps(items):
    steps, previous = [], None
    for item in items:
        block = item.block
        # Paragraphs, code blocks, lists and tables are each one reveal.
        # Only an explicit `splits` anchor can subdivide a source block.
        # Headings and answer labels accompany the first block they introduce.
        imports = previous and previous.node.tag == "pre" and all(
            line.startswith("import ") for line in previous.node.text.strip().splitlines())
        together = previous and (s.is_heading(previous) or
                                  "answer-heading" in previous.node.attrs.get("class", "") or
                                  (imports and s.is_heading(block)))
        if not steps or not together:
            steps.append([])
        steps[-1].append(block)
        previous = block
    return steps


def paginate(blocks, config, chapter, *, include_notes=False):
    if config.get("version") != 2 or set(config) - {"version", "pages", "splits"}:
        raise ValueError(f"{chapter}: invalid editorial config")
    all_items = source_items(blocks)
    main = split_items([i for i in all_items if i.block.kind == "main"], config, chapter)
    definitions, starts, ids = config.get("pages", []), [], set()
    for definition in definitions:
        if not {"at", "id", "label"} <= set(definition) or set(definition) - {"at", "id", "label", "column_at"}:
            raise ValueError(f"{chapter}: invalid page: {definition}")
        ident = definition["id"]
        if not re.fullmatch(r"[a-z][a-z0-9-]*", ident) or ident in ids:
            raise ValueError(f"{chapter}: duplicate or invalid editorial page id: {ident}")
        ids.add(ident)
        starts.append(locate(main, definition["at"], chapter))
    if not starts or starts[0] != 0 or starts != sorted(set(starts)):
        raise ValueError(f"{chapter}: editorial pages must cover the chapter in source order")
    pages = []
    for definition, start, end in zip(definitions, starts, starts[1:] + [len(main)]):
        group = main[start:end]
        column_key = ""
        if "column_at" in definition:
            column_index = locate(group, definition["column_at"], chapter)
            if column_index == 0 or group[column_index].block.join_key == group[column_index - 1].block.join_key:
                raise ValueError(f"{chapter}: second column must start at a new block inside the page")
            column_key = group[column_index].block.key
        # Opt-in notes interrupt the main text at their original source position.
        # A main page resumes after the note, keeping the default edition's
        # editorial boundaries intact when notes are omitted.
        note_orders = [i for i, b in enumerate(blocks) if b.kind != "main"] if include_notes else []
        runs = groupby(group, lambda item: sum(order < item.order for order in note_orders))
        for continuation, (_, run) in enumerate(runs):
            items = list(run)
            suffix = "" if not continuation else "-after-note-" + items[0].block.key
            page = s.Slide(chapter.lower() + "-" + definition["id"] + suffix, definition["label"],
                           items[0].block.section, "main", steps=page_steps(items), layout="compact", editorial=True,
                           column_at=column_key if any(i.block.key == column_key for i in items[1:]) else "")
            pages.append((items[0].order, page))
    before = "".join(i.block.source_text for i in all_items if i.block.kind == "main")
    after = "".join(b.source_text for _, p in pages for step in p.steps for b in step)
    if re.sub(r"\s", "", before) != re.sub(r"\s", "", after):
        raise ValueError(f"{chapter}: editorial content coverage mismatch")
    if include_notes:
        # Notes remain opt-in and retain their existing automatic pagination.
        for kind, run in groupby(enumerate(blocks), lambda pair: pair[1].kind):
            group = list(run)
            if kind == "main":
                continue
            pages.extend((group[0][0], page) for page in s.paginate([b for _, b in group], chapter))
        pages.sort(key=lambda pair: pair[0])
    return [page for _, page in pages]


def render_content(page, upto=None, *, reserve_space=False):
    sequence = [(b, stage) for stage, step in enumerate(page.steps) for b in step]
    result, column_index = [], None
    for _, run in groupby(sequence, lambda pair: pair[0].join_key or pair[0].key):
        all_parts = list(run)
        if all_parts[0][0].key == page.column_at:
            column_index = len(result)
        parts = [(b, stage) for b, stage in all_parts if reserve_space or upto is None or stage < upto]
        if not parts:
            continue
        first = parts[0][0].node
        if first.tag == "table":
            header, rows = [], []
            for block, stage in parts:
                for section in block.node.children:
                    if not isinstance(section, s.Node):
                        continue
                    if section.tag == "thead":
                        header.append(s.Node("thead", {"class": "step", "data-step": str(stage)}, section.children))
                    elif section.tag == "tbody":
                        for row in section.children:
                            if isinstance(row, s.Node):
                                attrs = dict(row.attrs, **{"class": "step", "data-step": str(stage)})
                                rows.append(s.Node(row.tag, attrs, row.children))
            result.append(s.Node("table", dict(first.attrs), header + [s.Node("tbody", children=rows)]).render())
        elif first.tag == "ol" and "data-exercise" in first.attrs:
            # A question may reveal several sentences, but remains one numbered
            # list item, including when an authored page boundary falls inside it.
            children = []
            for block, stage in parts:
                for item in block.node.children:
                    if isinstance(item, s.Node):
                        children.append(s.Node("span", {"class": "step", "data-step": str(stage)}, item.children))
            result.append(s.Node("ol", dict(first.attrs), [s.Node("li", children=children)]).render())
        elif first.tag in {"p", "pre", "ol", "ul"}:
            attrs, children = dict(first.attrs), []
            for block, stage in parts:
                node = block.node
                inside = node.children
                if first.tag == "pre" and len(inside) == 1 and isinstance(inside[0], s.Node) and inside[0].tag == "code":
                    inside = inside[0].children
                if first.tag in {"ol", "ul"}:
                    for child in inside:
                        if isinstance(child, s.Node):
                            child_attrs = dict(child.attrs, **{"data-step": str(stage)})
                            child_attrs["class"] = (child_attrs.get("class", "") + " step").strip()
                            children.append(s.Node(child.tag, child_attrs, child.children))
                else:
                    children.append(s.Node("span", {"class": "step", "data-step": str(stage)}, inside))
            if first.tag == "pre":
                children = [s.Node("code", children=children)]
            result.append(s.Node(first.tag, attrs, children).render())
        else:
            result.extend(s.Node("div", {"class": "step", "data-step": str(stage)}, [b.node]).render()
                          for b, stage in parts)
    if column_index is not None:
        result = ['<div class="slide-columns"><div class="slide-column">',
                  *result[:column_index], '</div><div class="slide-column">',
                  *result[column_index:], '</div></div>']
    content = "\n".join(result)
    if reserve_space and upto is not None:
        # Invisible future blocks still occupy space, so centering and column
        # positions stay identical at every PDF stage, just as in the browser.
        content = re.sub(r'data-step="(\d+)"', lambda m: m[0] +
                         (' data-unrevealed="" aria-hidden="true"' if int(m[1]) >= upto else ''), content)
    return content
