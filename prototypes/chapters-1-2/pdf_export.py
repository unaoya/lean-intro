"""Print the trial chapters using the shared book and slide PDF layouts."""
import html
import re
from urllib.parse import urljoin, urlsplit


def prepare_pdf_documents(here, book, titles, bodies, slide_document):
    preview = here / 'preview'
    names = {name.lower() for name in titles}
    intro = '<h1>第1〜5章 改稿試作</h1><p>型と項、型と命題、数学を記述する道具</p><ol>'
    for name, title in titles.items():
        intro += f'<li><a href="#ch-{name.lower()}">{html.escape(title)}</a></li>'
    intro += '</ol><p>練習の解答を開いた通読版です。補足は本文の関連箇所に配置しています。</p>'
    parts = [f'<section class="chapter" id="ch-index">{intro}</section>']
    for name, source in bodies.items():
        chapter = name.lower()
        body = source.replace('<details class="sol"', '<details open class="sol"')
        body = re.sub(r'id="(original-[^"]+)"', rf'id="{chapter}-\1"', body)

        def reading_link(match):
            href = match[1]
            path = urlsplit(href)
            if path.scheme or path.netloc:
                destination = href
            elif not path.path or path.path.removesuffix('.html') in names:
                fragment = path.fragment
                if fragment.startswith('original-'):
                    fragment = chapter + '-' + fragment
                destination = '#' + (fragment or 'ch-' + path.path.removesuffix('.html'))
            elif path.path.startswith('../../../docs/'):
                destination = 'https://unaoya.github.io/lean-intro/' + href.removeprefix('../../../docs/')
            else:
                destination = urljoin((preview / (chapter + '.html')).as_uri(), href)
            return f'href="{html.escape(destination, quote=True)}"'

        body = re.sub(r'href="([^"]+)"', reading_link, body)
        parts.append(f'<section class="chapter" id="ch-{chapter}">{body}</section>')
    reading_css = book.PDF_CSS + '''
pre, table, ol.exercise { break-inside: avoid; }
details.sol > summary { break-after: avoid; }
@page { @bottom-center { content: counter(page); font-size: 9pt; color: #646e76; } }
'''
    reading = book.page('第1〜5章 改稿試作 · 通読版', '\n'.join(parts), css=reading_css)

    # Trial section labels and pages are not published at the canonical URL.
    # Links from slide PDFs therefore open the matching local trial HTML.
    def slide_link(match):
        href = match[1]
        canonical = 'https://unaoya.github.io/lean-intro/'
        if href.startswith(canonical):
            relative = href.removeprefix(canonical)
            path = urlsplit(relative).path.removeprefix('slides/').removesuffix('.html')
            if path in names or path == 'index':
                href = urljoin((preview / 'index.html').as_uri(), relative)
        return f'href="{html.escape(href, quote=True)}"'

    slide_document = re.sub(r'href="([^"]+)"', slide_link, slide_document)
    slide_document = slide_document.replace('はじめての Lean · スライド</title>', '第1〜5章 改稿試作 · スライド</title>')
    # Use another 10px above the body while keeping a clear header gap. Keep the
    # available height independent of density so repeated print fitting is stable.
    slide_document = slide_document.replace('</style>', '</style><style>'
        '.print-slide[data-editorial] .print-content { top: 70px; }'
        '</style>', 1)
    documents = {'all': reading, 'slides': slide_document}
    scratch = here / 'tmp/pdfs'
    scratch.mkdir(parents=True, exist_ok=True)
    for name, document in documents.items():
        (scratch / (name + '.html')).write_text(document)
    return documents
