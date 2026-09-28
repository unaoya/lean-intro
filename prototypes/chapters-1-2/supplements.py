"""Render frozen originals separately; current notes live in the trial sources."""
import hashlib
import json


def render_original_references(here, repo, book, refs, slides, sections, chapters):
    names = ['03_InductiveTypes', '04_Exists']
    out = here / 'preview'
    reference = out / 'reference'
    reference.mkdir(parents=True, exist_ok=True)
    source, old_href = book.SRC, refs.href
    book.SRC = here / 'originals'
    audit = {}

    def original_href(label, chapter, sections):
        target = sections[label]
        return '../../../../docs/' + target.chapter.lower() + '.html#' + target.anchor

    try:
        refs.href = original_href
        for name in names:
            segments = book.parse(book.SRC / (name + '.lean'))
            start = 1 + sum(book.exercise_count(book.parse(repo / 'dev/src' / (n + '.lean')))
                            for n in chapters[:chapters.index(name)])
            body = book.render_chapter(name, segments, sections, exercise_start=start)
            root = slides.FragmentParser(body).root
            notes = [n for n in root.children if isinstance(n, slides.Node) and n.tag == 'aside']
            original_hashes = [hashlib.sha256(n.render().encode()).hexdigest() for n in notes]
            for i, note in enumerate(notes, 1):
                note.attrs['id'] = f'original-note-{i}'
            original_body = root.render()
            reference_banner = '<p><a href="../index.html">試作の目次</a> · コピー時点の元原稿（比較用）</p>'
            (reference / (name.lower() + '.html')).write_text(
                book.page(book.chapter_title(segments) + ' — 元原稿', reference_banner + original_body))
            audit[name] = {
                'original_notes': len(notes),
                'original_html_sha256': original_hashes,
                'appended_to_trial': False,
            }
    finally:
        book.SRC, refs.href = source, old_href
    (here / 'checks/supplements.json').write_text(json.dumps(audit, ensure_ascii=False, indent=2) + '\n')
