const {chromium}=require('/Users/sugakubunka/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
const fs=require('fs');
const path=require('path');
(async()=>{
 const browser=await chromium.launch({executablePath:'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',headless:true});
 const page=await browser.newPage({viewport:{width:1440,height:900},deviceScaleFactor:1});
 const failures=[];
 page.on('pageerror',e=>failures.push(e.message));
 const root=process.env.TRIAL_URL || 'http://127.0.0.1:8772/prototypes/chapters-1-2/preview';
 const reports=[];
 const screenshots=path.join(__dirname,'equality');
 fs.mkdirSync(screenshots,{recursive:true});
 for(const chapter of ['02_forall']){
  await page.goto(root+'/'+chapter+'.html',{waitUntil:'networkidle'});
  const reading=await page.evaluate(()=>{
   const xs=[...document.querySelectorAll('ol[data-exercise],details.sol')];
   const pairs=xs.length/2;
   const matched=xs.every((x,i)=>i%2?x.tagName==='DETAILS'&&x.dataset.exercise===xs[i-1].dataset.exercise:x.tagName==='OL');
   return {pairs,matched,mathRendered:document.querySelectorAll('.katex').length};
  });
  if(!reading.matched) failures.push(chapter+': question/answer order');
  const first=page.locator('details.sol').first();
  await first.locator('summary').click();
  if(await first.getAttribute('open')===null) failures.push(chapter+': answer toggle');
  reports.push({chapter,reading});
  await page.goto(root+'/slides/'+chapter+'.html',{waitUntil:'networkidle'});
  await page.evaluate(()=>document.fonts.ready);
  const math=await page.locator('.katex').count();
  if(await page.locator('.katex-error').count()) failures.push(chapter+': math rendering error');
  const before=await page.evaluate(()=>location.hash);
  await page.keyboard.press('ArrowRight');
  const after=await page.evaluate(()=>location.hash);
  if(before===after) failures.push(chapter+': forward navigation');
  await page.keyboard.press('ArrowLeft');
  if(await page.evaluate(()=>location.hash)!==before) failures.push(chapter+': backward navigation');
  await page.keyboard.press('m');
  if(!await page.locator('#toc').evaluate(x=>x.open)) failures.push(chapter+': contents');
  await page.locator('#close-toc').click();
  const slides=await page.locator('.slide').evaluateAll(xs=>xs.map(x=>({id:x.id,label:x.dataset.label,steps:Math.max(...[...x.querySelectorAll('[data-step]')].map(y=>+y.dataset.step))+1})));
  for (const size of [{width:1440,height:900},{width:1280,height:800}]){
   await page.setViewportSize(size);
   const overflow=[];
   for(const slide of slides){
    await page.evaluate(({id,steps})=>{location.hash='#'+id+'/'+steps;},slide);
    await page.evaluate(()=>new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve))));
    const result=await page.evaluate(()=>{
     const v=document.getElementById('viewport'),a=document.querySelector('.slide:not([hidden])');
     return {overflow:v.scrollHeight-v.clientHeight,height:Math.round(a.getBoundingClientRect().height),available:v.clientHeight-48,density:a.dataset.density||'normal',text:a.innerText.slice(0,95)};
    });
    if(result.overflow>3) overflow.push({...slide,...result});
   }
   if(overflow.length) failures.push(chapter+': '+size.width+'×'+size.height+' overflow');
   reports.push({chapter,viewport:size,mathRendered:math,pages:slides.length,overflow});
  }
  await page.setViewportSize({width:1440,height:900});
  const picks=['monotone-exercise','cancellation-map-exercise','rfl-implicit','rfl','equality-diagonal','equality-minimality','equality-induction','eq-symm','eq-trans','congr-arg','equality-tools','checking-original','original-axioms','original-interpretation'];
  for(const suffix of picks){
   const slide=slides.find(x=>x.id.endsWith('-'+suffix));if(!slide)continue;
   await page.evaluate(({id,steps})=>location.hash='#'+id+'/'+steps,slide);
   await page.evaluate(()=>new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve))));
   await page.screenshot({path:path.join(screenshots,chapter+'-'+suffix+'.png')});
  }
 }
 fs.writeFileSync(path.join(__dirname,'equality-browser-audit.json'),JSON.stringify({failures,reports},null,2));
 console.log(JSON.stringify({failures,reports},null,2));
 await browser.close();
})().catch(e=>{console.error(e);process.exit(1)});
