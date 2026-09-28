const {chromium}=require(require('path').join(require('os').homedir(), '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright'));
const {pathToFileURL, fileURLToPath}=require('url');
const fs=require('fs');
const path=require('path');
(async()=>{
 const browser=await chromium.launch({executablePath:'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',headless:true});
 const page=await browser.newPage({viewport:{width:1440,height:900},deviceScaleFactor:1});
 const failures=[];
 page.on('pageerror',e=>failures.push(e.message));
 const root=process.env.TRIAL_URL || pathToFileURL(path.resolve(__dirname,'../preview')).href;
 const build=JSON.parse(fs.readFileSync(path.join(__dirname,'build.json')));
 let nextExercise=1;
 const reports=[];
 const screenshots=path.join(__dirname,'../tmp/pdfs/browser');
 fs.mkdirSync(screenshots,{recursive:true});
 for(const module of ['Index', ...Object.keys(build.exercises)]){
  const chapter=module.toLowerCase();
  await page.goto(root+'/'+chapter+'.html',{waitUntil:'networkidle'});
  const reading=await page.evaluate(()=>{
   const xs=[...document.querySelectorAll('ol[data-exercise],details.sol[data-exercise]')];
   const pairs=xs.length/2;
   const matched=xs.every((x,i)=>i%2?x.tagName==='DETAILS'&&x.dataset.exercise===xs[i-1].dataset.exercise:x.tagName==='OL');
   return {pairs,matched,mathRendered:document.querySelectorAll('.katex').length,mathErrors:document.querySelectorAll('.katex-error').length};
  });
  if(!reading.matched) failures.push(chapter+': question/answer order');
  const expected=build.exercises[module] || 0;
  const numbers=await page.locator('ol[data-exercise]').evaluateAll(xs=>xs.map(x=>+x.dataset.exercise));
  if(reading.pairs!==expected || numbers.join(',')!==Array.from({length:expected},(_,i)=>nextExercise+i).join(',')) failures.push(chapter+': exercise sequence');
  nextExercise+=expected;
  if(reading.mathErrors) failures.push(chapter+': reading math rendering');
  if(expected){
   const first=page.locator('details.sol[data-exercise]').first();
   await first.locator('summary').click();
   if(await first.getAttribute('open')===null) failures.push(chapter+': answer toggle');
  }
  const links=await page.locator('a[href]').evaluateAll(xs=>xs.map(x=>x.href));
  const broken=[];
  for(const href of links){
   const target=new URL(href);
   if(target.protocol!=='file:')continue;
   const filename=fileURLToPath(target);
   if(!fs.existsSync(filename)){broken.push(href);continue;}
   const anchor=decodeURIComponent(target.hash.slice(1));
   if(anchor && filename.endsWith('.html') && !fs.readFileSync(filename,'utf8').includes('id="'+anchor+'"'))broken.push(href);
  }
  if(broken.length) failures.push(chapter+': broken links');
  reading.brokenLinks=broken;
  reports.push({chapter,reading});
  if(!build.slides[module]) continue;
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
  if(slides.length!==build.slides[module].pages || slides.reduce((n,x)=>n+x.steps,0)!==build.slides[module].steps) failures.push(chapter+': slide count');
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
  const picks=['checking-example','expected-types','sorry','infoview','check-codomain','composition-term','checking-outer','rfl','eq-symm','sum-type','sum-match','sum-injective','anonymous','instance-search','point-pair-proof','fin-constructor'];
  for(const suffix of picks){
   const slide=slides.find(x=>x.id.endsWith('-'+suffix));if(!slide)continue;
   await page.evaluate(({id,steps})=>location.hash='#'+id+'/'+steps,slide);
   await page.evaluate(()=>new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve))));
   await page.screenshot({path:path.join(screenshots,chapter+'-'+suffix+'.png')});
  }
 }
 fs.writeFileSync(path.join(__dirname,'browser-audit.json'),JSON.stringify({failures,reports},null,2));
 console.log(JSON.stringify({failures,reports},null,2));
 await browser.close();
 if(failures.length)process.exitCode=1;
})().catch(e=>{console.error(e);process.exit(1)});
