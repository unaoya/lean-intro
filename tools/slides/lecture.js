(() => {
  'use strict';
  const $ = id => document.getElementById(id);
  const root = document.documentElement;
  const slides = Array.from(document.querySelectorAll('.slide'));
  const viewport = $('viewport');
  const optional = $('optional');
  let active = slides[0];
  let step = 0;
  let reading = false;

  function included() {
    return slides.filter(slide => optional.checked || slide.dataset.kind === 'main');
  }
  function steps(slide = active) { return Array.from(slide.querySelectorAll(':scope > .step')); }
  function updateHash() {
    const hash = `#${active.id}/${step + 1}`;
    if (location.hash !== hash) history.replaceState(null, '', hash);
  }
  function readHash() {
    const match = location.hash.match(/^#([a-z0-9-]+)(?:\/(\d+))?$/);
    if (!match) return;
    const target = slides.find(slide => slide.id === match[1]);
    if (!target) return;
    active = target;
    step = Math.min(Math.max(Number(match[2] || 1) - 1, 0), steps().length - 1);
    if (active.dataset.kind !== 'main') optional.checked = true;
  }
  function render({scroll = false, announce = true} = {}) {
    const visible = included();
    const index = visible.indexOf(active);
    root.classList.toggle('include-optional', optional.checked);
    for (const slide of slides) {
      slide.hidden = reading ? !visible.includes(slide) : slide !== active;
      steps(slide).forEach((fragment, i) => {
        const hidden = !reading && i > (slide === active ? step : 0);
        fragment.toggleAttribute('data-unrevealed', hidden);
        fragment.inert = hidden;
        fragment.setAttribute('aria-hidden', String(hidden));
      });
    }
    $('counter').textContent = `${index + 1} / ${visible.length}`;
    $('step-count').textContent = reading ? '通読' : `表示 ${step + 1} / ${steps().length}`;
    $('next').textContent = step < steps().length - 1 && !reading ? '続きを表示 →' : '次の画面 →';
    $('previous').disabled = reading || (index === 0 && step === 0);
    $('next').disabled = reading || (index === visible.length - 1 && step === steps().length - 1);
    $('progress-fill').style.width = `${((index + (step + 1) / steps().length) / visible.length) * 100}%`;
    $('reading-mode').setAttribute('aria-pressed', String(reading));
    $('reading-mode').textContent = reading ? '講義に戻る' : '通読';
    if (announce) $('announcement').textContent = `${index + 1} / ${visible.length}、${active.dataset.label}、表示 ${step + 1} / ${steps().length}`;
    updateHash();
    if (scroll) viewport.scrollTop = 0;
  }
  function navigate(direction) {
    if (reading) return;
    const visible = included();
    const index = visible.indexOf(active);
    let changedSlide = false;
    if (direction > 0) {
      if (step < steps().length - 1) step++;
      else if (index < visible.length - 1) {
        active = visible[index + 1]; step = 0; changedSlide = true;
      }
    } else {
      if (step > 0) step--;
      else if (index > 0) {
        active = visible[index - 1]; step = steps().length - 1; changedSlide = true;
      }
    }
    render({scroll: changedSlide});
    if (!changedSlide && direction > 0) {
      const fragment = steps()[step];
      const frame = viewport.getBoundingClientRect();
      const rect = fragment.getBoundingClientRect();
      if (rect.top > frame.bottom - 70) fragment.scrollIntoView({block: 'start'});
    }
  }
  function jump(target) {
    active = target;
    step = 0;
    render({scroll: !reading});
    if (reading) active.scrollIntoView({block: 'start'});
  }
  function showContents() {
    const list = $('toc-list');
    list.replaceChildren();
    included().forEach((slide, i) => {
      const li = document.createElement('li');
      const button = document.createElement('button');
      button.type = 'button';
      const number = document.createElement('span');
      number.className = 'toc-number';
      number.textContent = `${i + 1}`;
      button.append(number, document.createTextNode(slide.dataset.label));
      if (slide === active) button.setAttribute('aria-current', 'page');
      button.addEventListener('click', () => { $('toc').close(); jump(slide); });
      li.append(button); list.append(li);
    });
    $('toc').showModal();
  }
  function toggleReading() {
    if (reading) {
      const frame = viewport.getBoundingClientRect();
      active = included().find(slide => slide.getBoundingClientRect().bottom > frame.top + 40) || active;
      step = 0;
    }
    reading = !reading;
    root.classList.toggle('reading', reading);
    render({scroll: !reading});
    if (reading) active.scrollIntoView({block: 'start'});
  }
  optional.addEventListener('change', () => {
    if (!optional.checked && active.dataset.kind !== 'main') {
      const index = slides.indexOf(active);
      active = slides.slice(index + 1).find(slide => slide.dataset.kind === 'main') || slides[0];
      step = 0;
    }
    render({scroll: !reading});
  });
  $('previous').addEventListener('click', () => navigate(-1));
  $('next').addEventListener('click', () => navigate(1));
  $('contents').addEventListener('click', showContents);
  $('close-toc').addEventListener('click', () => $('toc').close());
  $('reading-mode').addEventListener('click', toggleReading);
  $('chapter-select').addEventListener('change', event => { location.href = event.target.value; });
  $('fullscreen').addEventListener('click', async () => {
    try {
      if (document.fullscreenElement) await document.exitFullscreen();
      else await root.requestFullscreen();
    } catch {
      $('hint').textContent = 'ブラウザの全画面表示をご利用ください';
    }
  });
  document.addEventListener('fullscreenchange', () => {
    $('fullscreen').textContent = document.fullscreenElement ? '全画面解除' : '全画面';
  });
  document.addEventListener('keydown', event => {
    if ($('toc').open || event.altKey || event.ctrlKey || event.metaKey) return;
    if (event.target.closest('input:not([type="checkbox"]), textarea, select, summary, a') || event.target.isContentEditable) return;
    if (event.code === 'Space' && event.target.closest('input[type="checkbox"]')) return;
    if ((event.code === 'Space' || event.key === 'Enter') && event.target.closest('button')) return;
    if (event.key === 'ArrowRight' || event.key === 'PageDown' || event.code === 'Space') {
      if (reading) return;
      event.preventDefault(); navigate(event.shiftKey ? -1 : 1);
    } else if (event.key === 'ArrowLeft' || event.key === 'PageUp') {
      if (reading) return;
      event.preventDefault(); navigate(-1);
    } else if (event.key === 'Home' && !reading) {
      event.preventDefault(); jump(included()[0]);
    } else if (event.key === 'End' && !reading) {
      event.preventDefault(); active = included().at(-1); step = steps().length - 1; render({scroll:true});
    } else if (event.key.toLowerCase() === 'm') showContents();
  });
  window.addEventListener('hashchange', () => { readHash(); render({scroll: true}); });
  // Published section links can be opened directly in the slide edition too.
  const sectionTarget = location.hash.startsWith('#sec-') &&
    slides.find(slide => slide.dataset.section === location.hash.slice(5));
  if (sectionTarget) active = sectionTarget;
  readHash();
  root.classList.add('enhanced');
  render({announce: false});
})();
