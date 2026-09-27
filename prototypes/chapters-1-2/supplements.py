"""Keep the original optional material intact, including code and solutions.

The frozen original Lean files remain the source. Their notes are rendered in a
separate optional appendix; references point to the original reading edition so
that definitions deferred to chapter 5 remain accessible in context.
"""
import copy
import hashlib
import json


def preserve_supplements(here, repo, book, refs, slides, sections, chapters):
    names = ['03_InductiveTypes', '04_Exists']
    out = here / 'preview'
    reference = out / 'reference'
    reference.mkdir(parents=True, exist_ok=True)
    source, old_href = book.SRC, refs.href
    book.SRC = here / 'originals'
    results, audit = {}, {}

    def original_href(label, chapter, sections):
        target = sections[label]
        return '../../../../docs/' + target.chapter.lower() + '.html#' + target.anchor

    def descendants(node):
        yield node
        for child in node.children:
            if isinstance(child, slides.Node):
                yield from descendants(child)

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
            appendix = ['<aside class="note note--optional" id="original-supplements">',
                        '<h2>元原稿から残した補足</h2>',
                        '<p>以下は元原稿の補足・先取りを、そのまま残したものです。補足内の練習番号も元原稿の番号です。'
                        '本文で後回しにした記法や定義が登場する場合は、各項の「元の文脈で読む」を参照してください。</p>']
            records = []
            for i, original in enumerate(notes, 1):
                note = copy.deepcopy(original)
                nodes = list(descendants(note))
                heading = next((n.text for n in nodes if n.tag in ('h2', 'h3', 'h4')), '補足の練習')
                for node in nodes:
                    # Label the old numbering without mixing it into the trial's
                    # exercise sequence or affecting the original wording.
                    if 'data-exercise' in node.attrs:
                        node.attrs['data-original-exercise'] = node.attrs.pop('data-exercise')
                    if node.tag == 'a' and node.attrs.get('href', '').startswith('../../../../docs/'):
                        node.attrs['href'] = node.attrs['href'].replace('../../../../docs/', '../../../docs/', 1)
                    if node.tag == 'a' and node.attrs.get('href', '').startswith('#'):
                        node.attrs['href'] = 'reference/' + name.lower() + '.html' + node.attrs['href']
                assert note.text == original.text, 'Original supplementary text changed'
                appendix.append(f'<p><a href="reference/{name.lower()}.html#original-note-{i}">元の文脈で読む</a></p>')
                appendix.append(note.render())
                records.append({'title': heading, 'original_html_sha256': original_hashes[i - 1],
                                'text_preserved': note.text == original.text})
            appendix.append('</aside>')
            results[name] = '\n'.join(appendix)
            audit[name] = {'notes': len(notes), 'records': records}
    finally:
        book.SRC, refs.href = source, old_href
    (here / 'checks/supplements.json').write_text(json.dumps(audit, ensure_ascii=False, indent=2) + '\n')
    return results
