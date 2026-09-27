const fs = require('fs');
const path = require('path');
const {pathToFileURL} = require('url');
const runtime = path.join(require('os').homedir(), '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
const {chromium} = require(process.env.PLAYWRIGHT_MODULE || runtime);
(async () => {
  const root = path.resolve(__dirname, '..');
  const browser = await chromium.launch({executablePath: process.env.CHROME || '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome', headless: true});
  const page = await browser.newPage({viewport: {width: 1280, height: 720}});
  const errors = [];
  page.on('pageerror', e => errors.push(e.message));
  const report = {};
  try {
    for (const name of ['all', 'slides']) {
      await page.goto(pathToFileURL(path.join(root, 'tmp/pdfs', name + '.html')).href, {waitUntil: 'networkidle'});
      await page.evaluate(() => document.fonts.ready);
      await page.emulateMedia({media: 'print'});
      await page.evaluate(() => window.dispatchEvent(new Event('beforeprint')));
      report[name] = await page.evaluate(() => {
        const all = [...document.querySelectorAll('.print-slide')];
        const slides = all.map((slide, i) => {
          const content = slide.querySelector('.print-content');
          const body = slide.querySelector('.print-body');
          return {page: i + 1, label: slide.dataset.label, section: slide.dataset.section,
            stage: slide.querySelector('.print-foot').innerText,
            overflow: Math.round(body.getBoundingClientRect().height - content.clientHeight),
            density: slide.dataset.density || 'normal'};
        });
        return {math: document.querySelectorAll('.katex').length, mathErrors: document.querySelectorAll('.katex-error').length,
          closedAnswers: document.querySelectorAll('details.sol:not([open])').length,
          exercises: document.querySelectorAll('ol[data-exercise]').length,
          originalNotes: document.querySelectorAll('aside[id$="original-supplements"] > aside').length,
          slidePages: slides.length, overflow: slides.filter(x => x.overflow > 2),
          lastStages: slides.filter((x, i) => i === slides.length - 1 || slides[i + 1].label !== x.label)};
      });
      if (!report[name].math || report[name].mathErrors) errors.push(name + ': math rendering');
      if (report[name].closedAnswers) errors.push(name + ': closed answers');
      if (report[name].overflow.length) errors.push(name + ': slide overflow');
    }
    if (report.all.exercises !== 55 || report.all.originalNotes !== 18) errors.push('all: exercises or notes missing');
    const expected = Object.values(JSON.parse(fs.readFileSync(path.join(__dirname, 'slides.json')))).reduce((n, x) => n + x.steps, 0);
    if (report.slides.slidePages !== expected) errors.push('slides: page count mismatch');
    fs.writeFileSync(path.join(__dirname, 'pdf-layout.json'), JSON.stringify({errors, report}, null, 2) + '\n');
    console.log(JSON.stringify({errors, all: {...report.all, lastStages: undefined}, slides: {...report.slides, lastStages: undefined}}, null, 2));
    if (errors.length) process.exitCode = 1;
  } finally { await browser.close(); }
})().catch(e => { console.error(e); process.exitCode = 1; });
