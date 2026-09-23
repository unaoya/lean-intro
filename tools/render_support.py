"""Edition-local support for prose that contains nested Lean comments."""

from pathlib import Path
import re


def parse(path: Path, *, with_line_numbers: bool = False) -> list:
    """Keep nested comment examples in prose, preserving source line numbers."""
    lines = path.read_text(encoding="utf-8").split("\n")
    segments = []
    code = []
    code_start = 0

    def append(kind, start, body):
        if kind == "code":
            while body and not body[0].strip():
                body.pop(0)
                start += 1
            while body and not body[-1].strip():
                body.pop()
        if body:
            segments.append((kind, start + 1, body) if with_line_numbers else (kind, body))

    i = 0
    while i < len(lines):
        line = lines[i]
        if not (line.startswith("/-!") or line.startswith("/--")):
            if not code:
                code_start = i
            code.append(line)
            i += 1
            continue
        append("code", code_start, code)
        code = []
        start = i
        kind = "prose" if line.startswith("/-!") else "doc"
        depth = 1
        body = []
        while i < len(lines):
            part = lines[i][3:].lstrip() if i == start else lines[i]
            end = None
            for token in re.finditer(r"/-|-/", part):
                depth += 1 if token.group() == "/-" else -1
                if depth == 0:
                    end = token.start()
                    break
            body.append(part[:end].rstrip() if end is not None else part)
            i += 1
            if end is not None:
                break
        if depth:
            raise ValueError(f"{path}:{start + 1}: unclosed prose comment")
        append(kind, start, body)
    append("code", code_start, code)
    return segments
