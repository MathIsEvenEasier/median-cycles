import {presets,setup,construct,crossing,cut,samples,median,mod} from './model.mjs';
const $=id=>document.getElementById(id);
const svg=(tag,attrs,text)=>`<${tag} ${Object.entries(attrs).map(([k,v])=>`${k}="${v}"`).join(' ')}>${text??''}</${tag}>`;
const sign=v=>v>0?'+':'−';
let m,trace,step=0,selected=0,generation=0,heroWord;
const selector=$('preset');
presets.forEach((v,i)=>{const o=document.createElement('option');o.value=i;o.textContent=v.name;selector.append(o);});
function load(){m=setup(presets[+selector.value].pairs);trace=construct(m);step=0;generation=0;heroWord=trace.states.at(-1).slice();selected=trace.flips[0]?.t??0;renderProjection();render();renderImage();}
function renderProjection(){
  $('projection-formula').textContent=`B = ${m.B}  ·  ℓ(v) = ${m.coefficients.map((c,j)=>`${c===1?'':c+'·'}v${'₀₁₂'[j]}`).join(' + ')}`;
  $('offset-table').innerHTML='<div class="offset-row offset-head"><span>offset a</span><span>ℓ(a)</span></div>'+m.pairs.map((a,i)=>`<div class="offset-row ${Math.abs(m.q[i])===m.p?'extreme':''}"><span>(${a.join(', ')})</span><span>${m.q[i]}</span></div>`).join('');
  $('projection-caption').textContent=`r = ${m.r} offset pairs; p = ${m.p}; N = ${m.N}. The orange row is the extreme pair. ${m.d===3?'The diagram uses an oblique view of the three coordinate axes; labels give projected offsets.':'The diagram includes the center and both signs of each offset.'}`;
  const scale=76/m.M,extreme=m.q.findIndex(q=>Math.abs(q)===m.p);
  let out='';for(let a=-m.M;a<=m.M;a++)for(let b=-m.M;b<=m.M;b++)out+=svg('circle',{cx:115+a*scale,cy:115-b*scale,r:1.5,fill:'#bcc8b7'});
  out+=svg('path',{d:'M20 115H210M115 20V210',stroke:'#cdd4c6',fill:'none'});
  m.pairs.forEach((a,i)=>[1,-1].forEach(s=>{const x=115+s*(m.d===3?(a[0]-.55*a[1]):a[0])*scale,y=115-s*(m.d===3?(a[2]-.5*a[1]):(a[1]??0))*scale;out+=svg('circle',{cx:x,cy:y,r:8,fill:i===extreme?'#d47a42':'#5a8051'});out+=svg('text',{x:x+10,y:y-8,fill:'#183c36','font-size':11},`${s*m.q[i]}`);}));
  out+=svg('rect',{x:110,y:110,width:10,height:10,fill:'#183c36'});$('mask-view').innerHTML=out;
  $('period-value').textContent=`This construction: N = ${m.N}, within the upper bound ${m.periodBound}.`;
}
function render(){
  const y=trace.states[step],done=step===trace.flips.length,c=crossing(m,y,selected),phi=cut(m,y);
  $('construction-status').textContent=done?'Every position certified':'Construction in progress';$('construction-status').className='badge'+(done?'':' pending');
  $('next-flip').disabled=done;$('finish').disabled=done;$('reset').disabled=step===0;
  $('flip-count').textContent=`${step} / ${m.flipBound} bound`;$('cut-count').textContent=`${phi} / ${m.N*m.k}`;$('cross-count').textContent=`${c} (need ≥ ${m.k})`;
  $('bound-value').textContent=`This mask: at most ${m.flipBound} ${m.flipBound===1?'flip':'flips'}. The illustrated run uses ${trace.flips.length}.`;
  let message=`At t = ${selected}, c(t) = ${c} and k = ${m.k}. Flipping this pair would change Φ by ${4*(m.k-c)>0?'+':''}${4*(m.k-c)}. `;
  message+=done?'Every position meets the inequality; the witness is complete.':c<m.k?'This pair can be improved. The button takes the first available improving pair.':`This pair needs no repair. Next improving pair: ${trace.flips[step].t} and ${trace.flips[step].t+m.p}.`;
  if(step>0){const f=trace.flips[step-1];message+=` Last flip: ${f.t} and ${f.t+m.p}, Φ: ${f.before} → ${f.after}.`;}
  $('flip-explanation').textContent=message;
  renderCycle(y);renderVotes(y,done);
  $('positions').replaceChildren();for(let t=0;t<m.N;t++){const b=document.createElement('button');b.textContent=t;b.setAttribute('aria-label',`Inspect position ${t}`);b.setAttribute('aria-pressed',String(t===selected));b.onclick=()=>{selected=t;render();$('positions').children[t].focus();};$('positions').append(b);}
}
function renderCycle(y){
  const pt=t=>[230+125*Math.sin(t/m.N*2*Math.PI),163-125*Math.cos(t/m.N*2*Math.PI)],lines=[];
  m.remaining.forEach(q=>y.forEach((v,t)=>{const [x1,y1]=pt(t),[x2,y2]=pt(mod(t+q,m.N)),opp=v!==y[mod(t+q,m.N)];lines.push(svg('line',{x1,y1,x2,y2,stroke:opp?'#719857':'#b7bdb0','stroke-width':opp?1.6:1,'stroke-dasharray':opp?'none':'3 5',opacity:.55}));}));
  const [x1,y1]=pt(selected),[x2,y2]=pt(mod(selected+m.p,m.N));lines.push(svg('line',{x1,y1,x2,y2,stroke:'#d47a42','stroke-width':3}));
  y.forEach((v,t)=>{const [x,y]=pt(t),r=m.N>18?10:14,active=t===selected||t===mod(selected+m.p,m.N);lines.push(svg('circle',{cx:x,cy:y,r,fill:v>0?'#b8d69d':'#f5f2e8',stroke:active?'#d47a42':'#183c36','stroke-width':active?3:1}));lines.push(svg('text',{x,y:y+4,'text-anchor':'middle','font-size':13,fill:'#183c36'},sign(v)));const [lx,ly]=[230+(125+r+12)*Math.sin(t/m.N*2*Math.PI),163-(125+r+12)*Math.cos(t/m.N*2*Math.PI)];lines.push(svg('text',{x:lx,y:ly+3,'text-anchor':'middle','font-size':10,fill:'#5f716a'},t));});
  $('cycle').innerHTML=lines.join('');$('cycle').setAttribute('aria-label',`Antipodal coloring of ${m.N} positions. Selected pair ${selected}, ${mod(selected+m.p,m.N)}. Signs: ${y.map(sign).join(' ')}.`);
}
function renderVotes(y,done){
  const s=samples(m,y,selected),opp=s.filter(v=>v.value!==y[selected]).length;
  $('vote-title').textContent=`Current coloring · center t = ${selected}, sign ${sign(y[selected])}`;
  $('votes').innerHTML=s.map((v,i)=>`<div class="vote ${v.value!==y[selected]?'opposes':''} ${v.extreme?'extreme':''}"><span>${i===0?'center':`${v.offset>0?'+':''}${v.offset}`}</span><strong>${sign(v.value)}</strong><span>${v.value!==y[selected]?'opposes':'agrees'}</span><span>position ${v.index}</span></div>`).join('');
  $('vote-summary').innerHTML=`<strong>${opp} opposing / ${2*m.r+1} samples</strong>${opp>=m.r+1?'This center flips.':'This center does not yet flip.'} ${done?'Every position now has a strict opposing majority.':`The construction is unfinished. Passing at one position is not enough; ${y.filter((_,t)=>samples(m,y,t).filter(v=>v.value!==y[t]).length<m.r+1).length} positions still fail.`}`;
}
function renderImage(){
  const side=m.d===1?Math.max(8,m.N):m.N;
  $('picture').style.gridTemplateColumns=`repeat(${side},1fr)`;$('picture').replaceChildren();
  for(let j=0;j<side;j++)for(let i=0;i<side;i++){const t=mod(i+(m.coefficients[1]??0)*j,m.N);const cell=document.createElement('span');cell.className=heroWord[t]<0?'minus':'';$('picture').append(cell);}
  $('hero-label').textContent=presets[+selector.value].name;$('generation').textContent=`${generation} · ${generation%2?'−x':'x'}`;
  $('image-caption').textContent=`The completed witness, independent of the construction controls below. ${m.d===1?'Rows repeat a one-dimensional word.':m.d===3?'A z = 0 slice of the three-dimensional periodic image.':'One periodic tile of the two-dimensional image.'} Green = +1; cream = −1. N = ${m.N}.`;
  $('picture').setAttribute('aria-label',`${presets[+selector.value].name} completed periodic witness, update ${generation}. Every pixel reverses on the next update.`);
}
selector.onchange=load;
$('next-flip').onclick=()=>{if(step<trace.flips.length){selected=trace.flips[step].t;step++;render();}};
$('finish').onclick=()=>{step=trace.flips.length;render();};
$('reset').onclick=()=>{step=0;selected=trace.flips[0]?.t??0;render();};
$('median-step').onclick=()=>{heroWord=median(m,heroWord);generation++;renderImage();};
load();
