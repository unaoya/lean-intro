#!/usr/bin/env python3
"""受講者用ファイルから、ブラウザ（Lean 4 Web）で開ける1ファイル版を作る。

LeanIntro/Original/*.lean は前の章を import しているので、そのままでは Lean 4 Web で動かない。
そこで各章について、import をたどって依存するファイルを依存順に並べ、1つのファイルにまとめる。

  依存する章   コメントと #check・#eval・#print・#reduce を除き、section … end で囲んで先頭に置く
               （open・variable などが後ろに漏れないようにするため）
  その章自身   import 行を除いて、そのまま後ろに置く

出力は ../docs/play/<章>.lean（GitHub Pages で公開される）。受講者は次の形のリンクで開く。

  https://live.lean-lang.org/#project=Stable&url=https://unaoya.github.io/lean-intro/play/<章>.lean

Lean 4 Web は url= のファイルを読み込むので、リンクの長さは章の大きさによらない。

使い方（dev/ で）:
    python3 tools/bundle.py            # 通常は lean2html.py から呼ばれる
    python3 tools/bundle.py --check    # 生成したファイルを lean で1つずつコンパイルして確かめる
    python3 tools/bundle.py --check --lean="lean +stable"   # Lean 4 Web と同じ stable 版で確かめる
    python3 tools/bundle.py --links    # 章ごとのリンクを Markdown の表で表示する
"""

from pathlib import Path
from urllib.parse import quote
import re
import shlex
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent   # dev/
REPO = ROOT.parent
LESSONS = REPO / "LeanIntro"
OUT = REPO / "docs" / "play"
PAGES = "https://unaoya.github.io/lean-intro/play/"
EDITOR = "https://live.lean-lang.org/#project=Stable&url="

IMPORT_RE = re.compile(r"^import\s+LeanIntro\.(Original|Solutions)\.«([^»]+)»\s*$")
HASH_CMD_RE = re.compile(r"^#(check|eval|print|reduce)\b")
IN_PREFIX_RE = re.compile(r"^(set_option|open)\b.*\bin\s*$")
HEADER_MARK = "dev/tools/student.py が自動生成する"


def module_path(kind: str, name: str) -> Path:
    return LESSONS / kind / f"{name}.lean"


def imports(path: Path) -> list[tuple[str, str]]:
    deps = []
    for line in path.read_text(encoding="utf-8").splitlines():
        m = IMPORT_RE.match(line)
        if m:
            deps.append((m.group(1), m.group(2)))
        elif line.startswith("import "):
            raise SystemExit(f"{path}: 教材外の import には対応していない: {line}")
    return deps


def dependency_order(kind: str, name: str) -> list[tuple[str, str]]:
    """(kind, name) が依存するモジュールを、依存される側が先に来る順で返す（自身は含まない）。"""
    order: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()

    def visit(mod: tuple[str, str]) -> None:
        if mod in seen:
            return
        seen.add(mod)
        for dep in imports(module_path(*mod)):
            visit(dep)
        order.append(mod)

    visit((kind, name))
    return order[:-1]


def strip_comments(src: str) -> str:
    """Lean のコメント（入れ子の /- -/ と --）を除く。文字列・文字リテラルの中は触らない。"""
    out = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if src.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if src.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif src.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    if src[i] == "\n":
                        out.append("\n")      # 行数の目安を保つ（後で空行はまとめる）
                    i += 1
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append(src[i:j + 1])
            i = j + 1
        elif c == "'" and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] in "_'!?₀₁₂₃₄₅₆₇₈₉")):
            m = re.match(r"'(\\.[^']*|[^'\\\n])'", src[i:])
            if m:
                out.append(m.group(0))
                i += len(m.group(0))
            else:
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def strip_hash_commands(src: str) -> str:
    """行頭の #check・#eval・#print・#reduce（字下げした継続行を含む）と、直前の `… in` を除く。"""
    lines = src.splitlines()
    kept: list[str] = []
    i = 0
    while i < len(lines):
        if HASH_CMD_RE.match(lines[i]):
            while kept and IN_PREFIX_RE.match(kept[-1]):
                kept.pop()
            i += 1
            while i < len(lines) and lines[i][:1] in (" ", "\t") and lines[i].strip():
                i += 1
            continue
        kept.append(lines[i])
        i += 1
    return "\n".join(kept)


def squeeze(src: str) -> str:
    lines = [line.rstrip() for line in src.splitlines()]
    out: list[str] = []
    for line in lines:
        if not line and (not out or not out[-1]):
            continue
        out.append(line)
    while out and not out[-1]:
        out.pop()
    return "\n".join(out)


def body(path: Path) -> list[str]:
    """import 行と自動生成の注意書きを除いた本文の行。"""
    lines = path.read_text(encoding="utf-8").splitlines()
    lines = [l for l in lines if not IMPORT_RE.match(l)]
    while lines and (HEADER_MARK in lines[0] or "LeanIntro/MyWork/" in lines[0] or not lines[0].strip()):
        lines.pop(0)
    return lines


def bundle(name: str) -> str:
    deps = dependency_order("Original", name)
    dep_blocks = []
    for kind, dep in deps:
        code = squeeze(strip_hash_commands(strip_comments("\n".join(body(module_path(kind, dep))))))
        label = f"{dep}（解答）" if kind == "Solutions" else dep
        dep_blocks.append(f"-- ─── {label} ───\nsection\n\n{code}\n\nend")

    chapter = "\n".join(body(module_path("Original", name)))
    if not dep_blocks:
        header = [
            f"-- はじめての Lean — {name}（ブラウザ版・自動生成）",
            "-- 書き換えた内容は、このページの URL に入っています。残したいときは URL をブックマークするか、",
            "-- コードをコピーして保存してください。元に戻すときは、テキストのリンクから開き直します。",
        ]
        return "\n".join(header) + "\n\n" + chapter.rstrip() + "\n"

    dep_text = "\n\n".join(dep_blocks)
    names = "・".join(f"{d}（解答）" if k == "Solutions" else d for k, d in deps)
    header = [
        f"-- はじめての Lean — {name}（ブラウザ版・自動生成）",
        f"-- 先頭には、この章が使う前の章（{names}）のコードをまとめてあります。",
        "-- 本章は「ここから本章」の行から始まります（{START} 行目。Ctrl+G で行番号へ移動できます）。",
        "-- 書き換えた内容は、このページの URL に入っています。残したいときは URL をブックマークするか、",
        "-- コードをコピーして保存してください。元に戻すときは、テキストのリンクから開き直します。",
        "",
        "-- ════════ 前の章のコード（読まなくてよい） ════════",
        "",
    ]
    marker = [
        "",
        f"-- ════════ ここから本章：{name} ════════",
        "",
    ]
    text = "\n".join(header) + dep_text + "\n" + "\n".join(marker)
    start = next(i for i, l in enumerate(text.splitlines(), 1) if l.startswith("-- ════════ ここから本章"))
    text = text.replace("{START}", str(start))
    return text + chapter.rstrip() + "\n"


def chapters() -> list[str]:
    return sorted(p.stem for p in (LESSONS / "Original").glob("*.lean"))


def link(name: str) -> str:
    return EDITOR + quote(PAGES + name + ".lean", safe="")


def write_all() -> list[Path]:
    OUT.mkdir(parents=True, exist_ok=True)
    written = []
    names = chapters()
    for stale in OUT.glob("*.lean"):
        if stale.stem not in names:
            stale.unlink()
    for name in names:
        path = OUT / f"{name}.lean"
        text = bundle(name)
        if not path.exists() or path.read_text(encoding="utf-8") != text:
            path.write_text(text, encoding="utf-8")
            written.append(path)
    return written


def check(lean: str = "lean") -> bool:
    ok = True
    for path in sorted(OUT.glob("*.lean")):
        r = subprocess.run([*shlex.split(lean), str(path)], capture_output=True, text=True)
        errors = [l for l in r.stdout.splitlines() if ": error" in l]
        status = "ok" if r.returncode == 0 else "NG"
        print(f"{status}  {path.name}  ({len(path.read_text(encoding='utf-8').splitlines())} 行)")
        for e in errors[:5]:
            print("    " + e)
        ok &= r.returncode == 0
    return ok


def main(argv: list[str]) -> int:
    written = write_all()
    if "--links" in argv:
        print("| 章 | ブラウザで開く |\n| --- | --- |")
        for name in chapters():
            print(f"| `{name}` | [開く]({link(name)}) |")
    elif written:
        print(f"ブラウザ版を更新: {', '.join(p.name for p in written)}")
    if "--check" in argv:
        lean = next((a.split("=", 1)[1] for a in argv if a.startswith("--lean=")), "lean")
        return 0 if check(lean) else 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
