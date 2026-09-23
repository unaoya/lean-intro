(() => {
  'use strict';

  // Measure the complete page, including unrevealed blocks. Font size and
  // authored page boundaries stay fixed; only line spacing and margins tighten.
  function fit(frame, content, available) {
    frame.removeAttribute('data-density');
    for (const density of ['tight', 'dense']) {
      if (content.getBoundingClientRect().height <= available + 1) break;
      frame.dataset.density = density;
    }
  }

  function fitPrint() {
    for (const slide of document.querySelectorAll('.print-slide[data-editorial]')) {
      const frame = slide.querySelector('.print-content');
      fit(slide, frame.querySelector('.print-body'), frame.clientHeight);
    }
  }

  window.LectureLayout = {fit};
  if (document.querySelector('.print-deck')) {
    fitPrint();
    window.addEventListener('load', fitPrint);
    window.addEventListener('beforeprint', fitPrint);
    document.fonts.ready.then(fitPrint);
  }
})();
