"""Stable section labels, generated source numbers, and HTML reference links.

Parsing Lean prose is delegated to lean2html.parse; this module only handles
metadata and references within the segments it returns.
"""

import re
from dataclasses import dataclass, field
from pathlib import Path

LABEL = r"[A-Za-z][A-Za-z0-9_.-]*"
HEADING_RE = re.compile(r"^## (?:(?P<number>[0-9]+)\. )?(?P<title>.+?) \{#sec-(?P<label>" + LABEL + r")\}$")
REF_RE = re.compile(r"\[(?P<text>[^\[\]\n]*(?:\n[^\[\]\n]*)?)\]\(#sec-(?P<label>" + LABEL + r")\)")
DISPLAY_RE = re.compile(r"(?:(?P<file>`[A-Za-z0-9_]+\.lean`)(?P<gap>\s*の?\s*))?(?P<number>[0-9]*)(?P<space>[ \t]*)(?P<unit>節?)")
SOL_RE = re.compile(r"^SOL (?P<label>" + LABEL + r"):(?P<item>[1-9][0-9]*)$")
BARE_RE = re.compile(r"(?<![A-Za-z0-9_`.])(?:[0-9]+[ \t]*節|[0-9]+(?=[ \t]*[〜～–-][ \t]*[0-9]+[ \t]*節))")
SECTION_STARTS = {"CH1": 0}


@dataclass
class Section:
    label: str
    chapter: str
    number: int
    title: str
    path: Path
    line: int
    supplements: list[str] = field(default_factory=list)

    @property
    def anchor(self) -> str:
        return "sec-" + self.label


@dataclass
class Result:
    sections: dict[str, Section] = field(default_factory=dict)
    errors: list[str] = field(default_factory=list)
    changes: list[str] = field(default_factory=list)
    originals: dict[Path, str] = field(default_factory=dict)
    updated: dict[Path, str] = field(default_factory=dict)

    def write(self) -> list[Path]:
        """Do not write any file when structural errors or concurrent edits exist."""
        if self.errors:
            raise ValueError("参照にエラーがあるため更新できません")
        paths = [p for p in self.updated if self.updated[p] != self.originals[p]]
        for path in self.originals:
            if path.read_text(encoding="utf-8") != self.originals[path]:
                raise ValueError(f"{path}: 検査後に変更されています。再実行してください")
        for path in paths:
            path.write_text(self.updated[path], encoding="utf-8")
        return paths


def diagnostic(path: Path, line: int, text: str, reason: str) -> str:
    return f"{path.name}:{line}: {text.replace(chr(10), ' ')} → {reason}"


def stripped(text: str) -> str:
    """Remove reference notation in displayed code; never insert links there."""
    return REF_RE.sub(lambda m: m['text'], text)


def href(label: str, chapter: str, sections: dict[str, Section]) -> str:
    target = sections[label]
    prefix = "" if target.chapter == chapter else target.chapter.lower() + ".html"
    return f"{prefix}#{target.anchor}"


def analyze(src: Path, chapters: list[str], sol_files: dict[str, str], parse) -> Result:
    result = Result()
    owners = {name: name for name in chapters}
    owners.update({sol: name for name, sol in sol_files.items()})
    # ExtraSol is compiled but is not embedded in the HTML.
    if "Extra" in owners and (src / "ExtraSol.lean").exists():
        owners["ExtraSol"] = "Extra"
    segments = {}
    edits: dict[Path, list[tuple[int, int, str]]] = {}
    offsets = {}

    def error(path, line, text, reason):
        result.errors.append(diagnostic(path, line, text, reason))

    def edit(path, start, end, replacement):
        if result.originals[path][start:end] == replacement:
            return
        edits[path].append((start, end, replacement))
        line = result.originals[path].count("\n", 0, start) + 1
        result.changes.append(diagnostic(path, line, result.originals[path][start:end], replacement))

    for name in owners:
        path = src / f"{name}.lean"
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as exc:
            error(path, 1, name, str(exc))
            continue
        result.originals[path] = text
        edits[path] = []
        offsets[path] = [0] + [m.end() for m in re.finditer("\n", text)]
        segments[path] = parse(path, with_line_numbers=True)
        if name not in chapters:
            continue
        number = SECTION_STARTS.get(name, 1)
        current = None
        for kind, first_line, lines in segments[path]:
            if kind != "prose":
                continue
            for i, line in enumerate(lines, first_line):
                if line.startswith("## "):
                    current = None
                    heading = HEADING_RE.fullmatch(line)
                    if not heading:
                        if re.match(r"^## [0-9]+\.", line) or "{#sec-" in line:
                            error(path, i, line, "番号つき見出しには固定ラベル {#sec-名前} が必要です")
                        continue
                    label = heading['label']
                    current = Section(label, name, number, heading['title'], path, i)
                    if label in result.sections:
                        other = result.sections[label]
                        error(path, i, line, f"ラベル重複（{other.path.name}:{other.line}）")
                    else:
                        result.sections[label] = current
                    start = offsets[path][i - 1]
                    raw_line = text[start:].split('\n', 1)[0]
                    start += raw_line.index(line)
                    # Only replace the prefix: the title may itself contain a reference.
                    edit(path, start, start + heading.start('title'), f"## {number}. ")
                    number += 1
                elif current is not None and re.match(r"^### 補足(?:[（: ]|$)", line):
                    current.supplements.append(line)

    for path, text in result.originals.items():
        ignored = set()
        raw_lines = text.split('\n')
        for i, line in enumerate(raw_lines, 1):
            if "refcheck-ignore" in line:
                ignored.add(i)
            if line.strip() == "-- refcheck: ignore-next-line":
                ignored.add(i + 1)
        masked = list(text)
        for match in REF_RE.finditer(text):
            start, end = match.span()
            line = text.count('\n', 0, start) + 1
            # Preserve line offsets while masking complete references.
            masked[start:end] = ['\n' if c == '\n' else ' ' for c in match[0]]
            section = result.sections.get(match['label'])
            if section is None:
                error(path, line, match[0], "参照先ラベルが存在しません")
                continue
            display = DISPLAY_RE.fullmatch(match['text'])
            if display is None or not (display['number'] or display['unit']):
                error(path, line, match[0], "表示は「節」「N節」「N」または `X.lean` 付きで指定してください")
                continue
            prefix = ""
            if display['file']:
                prefix = f"`{section.chapter}.lean`" + display['gap']
            elif owners[path.stem] != section.chapter:
                prefix = f"`{section.chapter}.lean` "
            value = prefix + str(section.number) + display['space'] + display['unit']
            edit(path, match.start('text'), match.end('text'), value)
            following = text[end:]
            keyword = re.match(r"（([^）\n]+)）", following)
            if keyword and keyword[1].replace('`', '') not in section.title.replace('`', ''):
                error(path, line, match[0], f"キーワード「{keyword[1]}」が節題「{section.title}」にありません")
            if following.startswith("の補足") and not section.supplements:
                error(path, line, match[0], "参照先の節に補足がありません")
        unmarked = ''.join(masked)
        for match in BARE_RE.finditer(unmarked):
            line = text.count('\n', 0, match.start()) + 1
            if line not in ignored:
                error(path, line, match[0], "固定ラベルのない節参照です。[節](#sec-名前) にしてください")
        # Malformed reserved links must not silently fall back to plain text.
        for match in re.finditer(r"\]\(#sec-", unmarked):
            line = text.count('\n', 0, match.start()) + 1
            error(path, line, raw_lines[line - 1], "参照リンクの構文が不正です")
        if path.stem in sol_files.values():
            owner = owners[path.stem]
            for kind, line_no, lines in segments[path]:
                first = lines[0].strip() if lines else ""
                if kind != "prose" or not first.startswith("SOL "):
                    continue
                marker = SOL_RE.fullmatch(first)
                section = result.sections.get(marker['label']) if marker else None
                if marker is None or any(l.strip() for l in lines[1:]):
                    error(path, line_no, first, "解答マーカーは SOL 固定ラベル:問題番号 としてください")
                elif section is None or section.chapter != owner:
                    error(path, line_no, first, "解答の節ラベルが対応する章にありません")
        new_text = text
        for start, end, replacement in sorted(edits[path], reverse=True):
            new_text = new_text[:start] + replacement + new_text[end:]
        result.updated[path] = new_text
    return result
