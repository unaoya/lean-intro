#!/usr/bin/env python3
"""Build only this trial's copies; canonical sources and docs are read-only."""
import argparse
import hashlib
import html
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--repo', type=Path, default=HERE.parent.parent)
parser.add_argument('--text-only', action='store_true', help='Skip slides while editing their boundaries')
parser.add_argument('--skip-lean', action='store_true', help='Reuse the last Lean check during layout editing')
args = parser.parse_args()
REPO = args.repo.resolve()
sys.path.insert(0, str(REPO / 'dev/tools'))
import lean2html as book
import refs
import slides

CHAPTERS = ['01_TypesAndTerms', '02_Forall']
SRC = HERE / 'src'
OUT = HERE / 'preview'

def source_hashes():
    return {str(p.relative_to(REPO)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted((REPO / 'dev/src').glob('*.lean'))}

before = source_hashes()
if not args.skip_lean:
    toolchain = (REPO / 'dev/lean-toolchain').read_text().strip().replace(':', '---').replace('/', '--')
    lean = Path.home() / '.elan/toolchains' / toolchain / 'bin/lean'
    if not lean.is_file():
        raise SystemExit(f'Lean compiler not found: {lean}')
    compiled = HERE / '.build'
    compiled.mkdir(exist_ok=True)
    (HERE / 'checks').mkdir(exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(compiled))
    for name in [*CHAPTERS, *(n + 'Sol' for n in CHAPTERS)]:
        cmd = [str(lean), '-Dpp.unicode.fun=true']
        if name in CHAPTERS:
            cmd += ['-o', str(compiled / (name + '.olean'))]
        cmd += [str(SRC / (name + '.lean'))]
        result = subprocess.run(cmd, cwd=SRC, env=env, text=True, capture_output=True)
        log = result.stdout + result.stderr
        (HERE / 'checks' / (name + '.log')).write_text(log)
        if result.returncode or 'warning:' in log:
            raise SystemExit(log)
        print(f'Lean OK: {name}')

# Index existing chapters for external references, replacing the two trial chapters.
# Do not invoke refs.Result.write(): that helper can rewrite canonical sources.
sections = {}
for name in book.CHAPTERS:
    path = SRC / (name + '.lean') if name in CHAPTERS else REPO / 'dev/src' / (name + '.lean')
    for kind, line, lines in book.parse(path, with_line_numbers=True):
        if kind != 'prose':
            continue
        parent_number = None
        for offset, text in enumerate(lines):
            match = refs.HEADING_RE.fullmatch(text)
            if match:
                number = int(match['number']) if match['number'] else (parent_number or 1)
                parent_number = number
                label = match['label']
                if label in sections:
                    raise SystemExit(f'Duplicate section: {label}')
                sections[label] = refs.Section(label, name, number, match['title'], path, line + offset,
                                               level=len(match['marks']))

def trial_href(label, chapter, sections):
    target = sections[label]
    if target.chapter == chapter:
        prefix = ''
    elif target.chapter in CHAPTERS:
        prefix = target.chapter.lower() + '.html'
    else:
        prefix = '../../../docs/' + target.chapter.lower() + '.html'
    return prefix + '#' + target.anchor

refs.href = trial_href
book.SRC = SRC
book.CHAPTERS = CHAPTERS
slides.CONFIG = HERE / 'slides'
OUT.mkdir(exist_ok=True)
titles, bodies, counts = {}, {}, {}
exercise_start = 1
for name in CHAPTERS:
    for path in [SRC / (name + '.lean'), SRC / (name + 'Sol.lean')]:
        missing = [m['label'] for m in refs.REF_RE.finditer(path.read_text()) if m['label'] not in sections]
        if missing:
            raise SystemExit(f'{path.name}: unknown references {missing}')
    segments = book.parse(SRC / (name + '.lean'))
    titles[name] = book.chapter_title(segments)
    bodies[name] = book.render_chapter(name, segments, sections, exercise_start=exercise_start)
    counts[name] = book.exercise_count(segments)
    exercise_start += counts[name]

assert counts == {'01_TypesAndTerms': 27, '02_Forall': 12}, counts
banner = '<p class="trial-banner">第1・2章 改稿試作 · <a href="index.html">試作の目次</a></p>'
css = book.CSS + '\n.trial-banner{border-left:4px solid #386456;padding:12px 16px;background:#eff6f2;font-size:14px}\n'
for i, name in enumerate(CHAPTERS):
    intro = banner + f'<p><a href="slides/{name.lower()}.html">この章のスライド</a> · <a href="../src/{name}.lean">試作原稿</a></p>'
    (OUT / (name.lower() + '.html')).write_text(book.page(titles[name], intro + bodies[name], book.nav_html(i), css))

index_body = '<h1>第1・2章 改稿試作</h1><p>関数の項から、具体的な数学の証明へ。</p><ol>'
for name in CHAPTERS:
    index_body += f'<li><a href="slides/{name.lower()}.html">{html.escape(titles[name])}</a></li>'
index_body += '</ol><p>段落・コードブロックごとに表示します。矢印キーで進み、M で目次を開けます。</p>'
index = '<h1>第1・2章 改稿試作</h1><p>元の原稿をコピーして作った、相談用の改稿です。</p>'
index += '<p>第1章は項の作り方と練習の配置を整理し、第2章は具体的な四つの題材から証明を読みます。</p>'
for i, name in enumerate(CHAPTERS, 1):
    index += f'<h2>第{i}章 · {html.escape(titles[name])}</h2><p><a href="{name.lower()}.html">通読版</a> · <a href="slides/{name.lower()}.html">スライド版</a> · <a href="../src/{name}.lean">試作原稿</a></p>'
index += '<p><a href="../PLAN.md">相談で決めた方針</a> · <a href="../README.md">再生成の手順</a></p>'
(OUT / 'index.html').write_text(book.page('第1・2章 改稿試作', index))

stats = {}
if not args.text_only:
    for name in ['Index', *CHAPTERS]:
        if not (slides.CONFIG / (name + '.json')).exists():
            raise SystemExit(f'Author slide boundaries first: {name}')
    _, decks = slides.build(titles, bodies, CHAPTERS, OUT, head=book.KATEX_HEAD, index_body=index_body)
    for path in (OUT / 'slides').glob('*.html'):
        rendered = path.read_text().replace('<a href="index.html">はじめての Lean</a>',
                                           '<a href="index.html">はじめての Lean · 改稿試作</a>')
        rendered = rendered.replace(' · 講義用</title>', ' · 改稿試作</title>')
        path.write_text(rendered)
    stats = {n: {'pages': len(p), 'steps': sum(len(s.steps) for s in p)} for n, p in decks.items()}
    (HERE / 'checks/slides.json').write_text(json.dumps(stats, ensure_ascii=False, indent=2) + '\n')
after = source_hashes()
assert before == after, 'Canonical sources changed during trial build'
(HERE / 'checks/build.json').write_text(json.dumps({'exercises': counts, 'slides': stats,
    'canonical_sources_unchanged_during_build': before == after,
    'matches_initial_canonical_sources': before == json.loads((HERE / 'original-sha256.json').read_text())}, indent=2) + '\n')
print(f'Preview: {OUT / "index.html"}')
