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
parser.add_argument('--pdf', action='store_true', help='Also generate reading and slide PDFs in output/pdf/')
args = parser.parse_args()
if args.pdf and args.text_only:
    parser.error('--pdf cannot be combined with --text-only')
REPO = args.repo.resolve()
sys.path.insert(0, str(REPO / 'dev/tools'))
import lean2html as book
import refs
import slides
from supplements import render_original_references
from pdf_export import prepare_pdf_documents

CANONICAL_CHAPTERS = list(book.CHAPTERS)
CHAPTERS = ['01_TypesAndTerms', '02_Forall', '03_InductiveTypes', '04_Exists', '05_MathematicalTools']
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

# Retain old labels as references to the canonical text; trial labels take precedence.
# Do not invoke refs.Result.write(): that helper can rewrite canonical sources.
def index_sections(names, root):
    result = {}
    for name in names:
        path = root / (name + '.lean')
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
                    if label in result:
                        raise SystemExit(f'Duplicate section: {label}')
                    result[label] = refs.Section(label, name, number, match['title'], path, line + offset,
                                                 level=len(match['marks']))
    return result

canonical_sections = index_sections(CANONICAL_CHAPTERS, REPO / 'dev/src')
sections = canonical_sections | index_sections(CHAPTERS, SRC)
render_original_references(HERE, REPO, book, refs, slides, canonical_sections, CANONICAL_CHAPTERS)

def trial_href(label, chapter, sections):
    target = sections[label]
    if target.path.parent != SRC:
        prefix = '../../../docs/' + target.chapter.lower() + '.html'
    elif target.chapter == chapter:
        prefix = ''
    else:
        prefix = target.chapter.lower() + '.html'
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

assert counts == {'01_TypesAndTerms': 27, '02_Forall': 12, '03_InductiveTypes': 10, '04_Exists': 6, '05_MathematicalTools': 16}, counts
banner = '<p class="trial-banner">第1〜5章 改稿試作 · <a href="index.html">試作の目次</a></p>'
css = book.CSS + '\n.trial-banner{border-left:4px solid #386456;padding:12px 16px;background:#eff6f2;font-size:14px}\n'
for i, name in enumerate(CHAPTERS):
    intro = banner + f'<p><a href="slides/{name.lower()}.html">この章のスライド</a> · <a href="../src/{name}.lean">試作原稿</a></p>'
    (OUT / (name.lower() + '.html')).write_text(book.page(titles[name], intro + bodies[name], book.nav_html(i), css))

index_body = '<h1>第1〜5章 改稿試作</h1><p>関数と証明から、数学を記述する道具へ。</p><ol>'
for name in CHAPTERS:
    index_body += f'<li><a href="slides/{name.lower()}.html">{html.escape(titles[name])}</a></li>'
index_body += '</ol><p>段落・コードブロックごとに表示します。矢印キーで進み、M で目次を開けます。</p>'
index = '<h1>第1〜5章 改稿試作</h1><p>元の原稿をコピーして作った、相談用の改稿です。</p>'
index += '<p>関数と依存関数、具体的な数学の証明、帰納型、存在量化と論理、構造体・部分型・集合を順に扱います。</p>'
for i, name in enumerate(CHAPTERS, 1):
    index += f'<h2>第{i}章 · {html.escape(titles[name])}</h2><p><a href="{name.lower()}.html">通読版</a> · <a href="slides/{name.lower()}.html">スライド版</a> · <a href="../src/{name}.lean">試作原稿</a></p>'
if args.pdf or all((HERE / 'output/pdf' / name).exists() for name in ['all.pdf', 'slides.pdf']):
    index += '<h2>PDF</h2><p><a href="../output/pdf/all.pdf">通読版PDF</a> · <a href="../output/pdf/slides.pdf">スライド版PDF（表示段階ごと）</a></p>'
index += '<p>補足は、改稿した本文の関連箇所に配置しています。比較用の元原稿は <code>originals/</code> に保存しています。</p>'
index += '<p><a href="../README.md">再生成の手順</a></p>'
(OUT / 'index.html').write_text(book.page('第1〜5章 改稿試作', index))

stats = {}
if not args.text_only:
    for name in ['Index', *CHAPTERS]:
        if not (slides.CONFIG / (name + '.json')).exists():
            raise SystemExit(f'Author slide boundaries first: {name}')
    slide_document, decks = slides.build(titles, bodies, CHAPTERS, OUT, head=book.KATEX_HEAD, index_body=index_body)
    for path in (OUT / 'slides').glob('*.html'):
        rendered = path.read_text().replace('<a href="index.html">はじめての Lean</a>',
                                           '<a href="index.html">はじめての Lean · 改稿試作</a>')
        rendered = rendered.replace(' · 講義用</title>', ' · 改稿試作</title>')
        path.write_text(rendered)
    stats = {n: {'pages': len(p), 'steps': sum(len(s.steps) for s in p)} for n, p in decks.items()}
    (HERE / 'checks/slides.json').write_text(json.dumps(stats, ensure_ascii=False, indent=2) + '\n')
if args.pdf:
    documents = prepare_pdf_documents(HERE, book, titles, bodies, slide_document)
    book.ROOT = HERE  # Only controls the PDF writer's output-path log.
    pdf_out = HERE / 'output/pdf'
    pdf_out.mkdir(parents=True, exist_ok=True)
    for name, document in documents.items():
        book.write_pdf(document, pdf_out / (name + '.pdf'))
after = source_hashes()
assert before == after, 'Canonical sources changed during trial build'
(HERE / 'checks/build.json').write_text(json.dumps({'exercises': counts, 'slides': stats,
    'canonical_sources_unchanged_during_build': before == after,
    'matches_initial_canonical_sources': before == json.loads((HERE / 'original-sha256.json').read_text())}, indent=2) + '\n')
print(f'Preview: {OUT / "index.html"}')
