import {presets,setup,construct,crossing,cut,samples,median,mod,latticeValue,comparePatterns,periodTwoObstruction} from './model.mjs?v=a6e4cf7';
const $=id=>document.getElementById(id);
const svg=(tag,attrs,text)=>`<${tag} ${Object.entries(attrs).map(([k,v])=>`${k}="${v}"`).join(' ')}>${text??''}</${tag}>`;
const sign=v=>v>0?'+':'−';
let m,trace,step=0,selected=0,generation=0,heroWord,pattern='constructed',zLayer=0;
const selector=$('preset');
presets.forEach((v,i)=>{const o=document.createElement('option');o.value=i;o.textContent=v.name;selector.append(o);});
const alternating=()=>Array.from({length:m.N},(_,t)=>t%2?-1:1);
const inputWord=()=>pattern==='constructed'?trace.states.at(-1):alternating();
function choosePattern(value){pattern=value;generation=0;heroWord=inputWord().slice();renderImage();}
function load(){m=setup(presets[+selector.value].pairs);trace=construct(m);step=0;zLayer=0;$('z-layer').max=m.N-1;selected=trace.flips[0]?.t??0;renderProjection();render();renderComparison();choosePattern('constructed');}
function voteRange(y){const counts=y.map((_,t)=>samples(m,y,t).filter(v=>v.value!==y[t]).length);return [Math.min(...counts),Math.max(...counts)];}
function wordRows(id,y){
  const next=median(m,y);
  $(id).innerHTML=[['Input',y],['After median',next]].map(([label,word])=>`<div class="word-row"><span>${label}</span><div class="word-cells" style="grid-template-columns:repeat(${m.N},minmax(0,1fr))" role="img" aria-label="${label}: ${word.map(v=>v>0?1:0).join('')}">${word.map(v=>`<span class="${v<0?'minus':''}">${v>0?1:0}</span>`).join('')}</div></div>`).join('');
}
function renderComparison(){
  const y=trace.states.at(-1),alt=alternating(),[min,max]=voteRange(y),[opposing]=voteRange(alt),total=2*m.r+1,works=opposing>=m.r+1;
  const relation=comparePatterns(y,alt),same=relation==='identical';
  const obstruction=periodTwoObstruction(m),motif=Array(m.d).fill('2').join(' × ');
  $('comparison-label').textContent=same?'The same filter, the same input':'Compare the two constructions';
  $('comparison-heading').textContent=same?'Here the construction gives exactly the checkerboard.':relation==='complement'?'Here the construction swaps the checkerboard colors.':'A checkerboard is not a universal answer.';
  if(obstruction.locked)$('comparison-heading').textContent=m.d===1?'Every period-2 input gets stuck.':`Every repeating ${motif} block gets stuck.`;
  $('period-two-obstruction').hidden=!obstruction.locked;
  $('period-two-obstruction').innerHTML=obstruction.locked?`<strong>Why the obvious small patterns cannot work</strong><p>In any input repeating every 2 cells in each coordinate, an offset with all coordinates even returns the center’s color. This mask contains ${obstruction.evenPairs.map(a=>'±('+a.join(', ')+')').join(', ')}. Those ${2*obstruction.evenPairs.length} samples, together with the center, give <b>${obstruction.agreeing} agreeing votes out of ${obstruction.total}</b>: a strict majority. Every such input is a fixed point. This includes all checkerboards and stripes built from a repeating ${motif} block.</p><p>The construction below uses period ${m.N}. After ${trace.flips.length} improving flips, every point has ${min===max?min:`${min}–${max}`} opposing votes, so every point changes. A strict majority is enough; some neighbors may still agree with the center.</p>`:'';
  $('comparison-identity').hidden=relation==='different';
  $('comparison-identity').textContent=same?`The two cards below are identical. For this mask, the general construction ends at the ordinary checkerboard; both inputs and both outputs match. The displayed ${m.N}-entry word simply repeats the two-entry block 10.`:relation==='complement'?'The two patterns differ only by exchanging 0 and 1. They are the two phases of the same checkerboard cycle.':'';
  $('word-explanation').textContent=m.d===1?'Each row below is one spatial period of a one-dimensional input.':`The rows below show a one-dimensional encoding, not a ${m.d}D picture. The lattice color at (${m.d===3?'x, y, z':'x, y'}) is word[(${m.d===3?`x + ${m.B}y + ${m.B*m.B}z`:`x + ${m.B}y`}) mod ${m.N}]. ${m.d===3?'The three-layer view above shows the actual 3D configuration.':''}`;
  $('hero-mask').textContent=`W = {0, ${m.pairs.map(a=>m.d===1?'±'+a[0]:'±('+a.join(', ')+')').join(', ')}}`;
  $('comparison-explanation').textContent=m.d===1?`The selected filter reads the center and the pixels at distances ${m.pairs.map(a=>Math.abs(a[0])).join(', ')} in both directions. In an alternating input, an odd distance changes the color; an even distance preserves it.`:`In a checkerboard, an offset changes the color exactly when the sum of its coordinates is odd. Symmetry alone does not ensure that enough offsets change color. All base-B coefficients are odd, so the alternating projected word gives this same lattice checkerboard.`;
  wordRows('alternating-rows',alt);wordRows('constructed-rows',y);
  $('alternating-verdict').innerHTML=`<strong>${opposing} opposing votes out of ${total} at every pixel.</strong> ${works?'Here, alternation works: every pixel flips. Try “Offsets 1, 2, 4” to see where this shortcut fails.':`The ${total-opposing} votes agreeing with the center win. This input is a fixed point: no pixel changes.`}`;
  $('constructed-verdict').innerHTML=`<strong>${min===max?min:`${min}–${max}`} opposing votes out of ${total} at every pixel.</strong> ${same?'This is exactly the same checkerboard as on the left. ':''}Every pixel has the required ${m.r+1} or more opposing votes. All pixels flip; applying the median again recovers the input.`;
}
function renderProjection(){
  $('projection-formula').textContent=`B = ${m.B}  ·  ℓ(v) = ${m.coefficients.map((c,j)=>`${c===1?'':c+'·'}v${'₀₁₂'[j]}`).join(' + ')}`;
  $('offset-table').innerHTML='<div class="offset-row offset-head"><span>offset a</span><span>ℓ(a)</span></div>'+m.pairs.map((a,i)=>`<div class="offset-row ${Math.abs(m.q[i])===m.p?'extreme':''}"><span>(${a.join(', ')})</span><span>${m.q[i]}</span></div>`).join('');
  $('projection-caption').textContent=`r = ${m.r} offset pairs; p = ${m.p}; N = ${m.N}. The orange row is the extreme pair. ${m.d===3?'The diagram uses an oblique view of the three coordinate axes; labels give projected offsets.':'The diagram includes the center and both signs of each offset.'}`;
  const extent=m.d===3?Math.max(...m.pairs.map(a=>Math.max(Math.abs(a[0]-.55*a[1]),Math.abs(a[2]-.5*a[1])))):m.M;
  const scale=76/extent,extreme=m.q.findIndex(q=>Math.abs(q)===m.p);
  let out='';
  if(m.d===3){
    out+=svg('path',{d:'M20 115H210M115 20V210M168 67L62 163',stroke:'#a2b59c',fill:'none'});
    out+=svg('text',{x:212,y:128,'font-size':12,fill:'#183c36'},'x');
    out+=svg('text',{x:49,y:178,'font-size':12,fill:'#183c36'},'y');
    out+=svg('text',{x:99,y:19,'font-size':12,fill:'#183c36'},'z');
  }else{
    for(let a=-m.M;a<=m.M;a++)for(let b=-m.M;b<=m.M;b++)out+=svg('circle',{cx:115+a*scale,cy:115-b*scale,r:1.5,fill:'#bcc8b7'});
    out+=svg('path',{d:'M20 115H210M115 20V210',stroke:'#cdd4c6',fill:'none'});
  }
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
  const is3D=m.d===3,relation=comparePatterns(trace.states.at(-1),alternating());
  $('picture').hidden=is3D;$('volume-view').hidden=!is3D;
  $('pattern-equivalence').hidden=relation==='different';
  $('pattern-equivalence').textContent=relation==='identical'?'Both choices give the same checkerboard for this mask.':'Both choices give the same checkerboard with colors exchanged.';
  const side=m.d===1?Math.max(8,m.N):m.N;
  $('picture').style.gridTemplateColumns=`repeat(${side},1fr)`;$('picture').replaceChildren();
  for(let j=0;j<side;j++)for(let i=0;i<side;i++){const t=mod(i+(m.coefficients[1]??0)*j,m.N);const cell=document.createElement('span');cell.className=heroWord[t]<0?'minus':'';$('picture').append(cell);}
  const seed=inputWord(),next=median(m,heroWord),changed=next.filter((v,t)=>v!==heroWord[t]).length,same=heroWord.every((v,t)=>v===seed[t]);
  $('hero-label').textContent=presets[+selector.value].name;$('generation').textContent=`${generation} · ${same?'input':'complement'}`;
  $('hero-word').textContent=heroWord.map(v=>v>0?'1':'0').join('');
  $('hero-outcome').textContent=changed===0?'No pixel changes. This input is a fixed point.':changed===m.N?'Every pixel flips. Two updates recover the input.':`${changed} of ${m.N} cycle positions change on the next update.`;
  $('show-constructed').setAttribute('aria-pressed',String(pattern==='constructed'));$('show-alternating').setAttribute('aria-pressed',String(pattern==='alternating'));
  $('image-caption').textContent=`${pattern==='constructed'?'The completed construction.':'The simple alternating input.'} ${m.d===1?'Rows repeat the same one-dimensional word.':is3D?'Each layer shows a 5 × 5 crop, with x and y from −2 to 2.':'A tile of the periodic two-dimensional image.'} Green = 1; cream = 0. The word above lists the ${m.N} cycle positions. The construction controls below are separate.`;
  $('picture').setAttribute('aria-label',`${presets[+selector.value].name}, ${pattern} input, update ${generation}. ${$('hero-outcome').textContent}`);
  if(is3D)renderVolume();
}
function renderVolume(){
  $('z-layer').value=zLayer;$('z-value').textContent=`z = ${zLayer}`;
  const center=[0,0,zLayer],centerValue=latticeValue(m,heroWord,center);
  const neighbors=m.pairs.flatMap(a=>[a,a.map(v=>-v)]);
  $('volume-layers').innerHTML=[-1,0,1].map(dz=>{
    let cells='';
    for(let y=2;y>=-2;y--)for(let x=-2;x<=2;x++){
      const value=latticeValue(m,heroWord,[x,y,zLayer+dz]),isCenter=x===0&&y===0&&dz===0,isNeighbor=neighbors.some(a=>a[0]===x&&a[1]===y&&a[2]===dz);
      cells+=`<span class="voxel ${value<0?'minus':''} ${isCenter?'center':''} ${isNeighbor?'neighbor':''}" title="(${x}, ${y}, ${zLayer+dz}): ${value>0?1:0}${isCenter?' — center':isNeighbor?' — mask neighbor':''}">${value>0?1:0}</span>`;
    }
    return `<div class="volume-layer"><strong>z = ${zLayer+dz}</strong><span>${dz<0?'Below':dz>0?'Above':'Central layer'}</span><div class="slice-grid" role="img" aria-label="Layer z equals ${zLayer+dz}. Central column value ${latticeValue(m,heroWord,[0,0,zLayer+dz])>0?1:0}. All cells are at the same time step ${generation}.">${cells}</div></div>`;
  }).join('');
  const offsets=[[0,0,0],...neighbors];
  const neighborLabels=offsets.map((a,i)=>i===0?'Center':`(${a.map(v=>v<0?'−'+(-v):v).join(',')})`);
  const values=offsets.map(a=>latticeValue(m,heroWord,a.map((v,j)=>v+center[j])));
  const opposing=values.filter(v=>v!==centerValue).length;
  const inLayer=neighbors.filter((a,i)=>a[2]===0&&values[i+1]!==centerValue).length;
  const above=neighbors.filter((a,i)=>a[2]>0&&values[i+1]!==centerValue).length;
  const below=neighbors.filter((a,i)=>a[2]<0&&values[i+1]!==centerValue).length;
  const layerValues=dz=>Array.from({length:25},(_,i)=>latticeValue(m,heroWord,[i%5-2,Math.floor(i/5)-2,zLayer+dz]));
  const layerRelation=comparePatterns(layerValues(0),layerValues(1));
  $('volume-votes').innerHTML=`<strong>${values.length} samples around (0, 0, ${zLayer})</strong><div class="voxel-votes">${values.map((v,i)=>`<span class="${v!==centerValue?'opposes':'agrees'} ${v>0?'one':'zero'} ${i===0?'center':''}" title="${i===0?'Selected center':v!==centerValue?'Opposes the center':'Agrees with the center'}"><small>${neighborLabels[i]}</small><b>${v>0?1:0}</b></span>`).join('')}</div><p>${opposing} of ${values.length} oppose the center: ${inLayer} in its layer, ${above} above, and ${below} below. ${Math.sign(values.reduce((s,v)=>s+v,0))!==centerValue?'The voxel flips.':'The voxel stays the same.'} Green borders mark opposing votes; orange marks the center.</p><p class="layer-relation">${layerRelation==='complement'?'The two adjacent layer crops have opposite colors at every position.':layerRelation==='identical'?'The two adjacent layer crops are identical.':'The two adjacent layer crops differ at some positions and agree at others.'} Off-layer samples have offsets ${neighbors.filter(a=>a[2]!==0).map(a=>'('+a.join(', ')+')').join(' and ')}.</p>`;
}
selector.onchange=load;
$('next-flip').onclick=()=>{if(step<trace.flips.length){selected=trace.flips[step].t;step++;render();}};
$('finish').onclick=()=>{step=trace.flips.length;render();};
$('reset').onclick=()=>{step=0;selected=trace.flips[0]?.t??0;render();};
$('median-step').onclick=()=>{heroWord=median(m,heroWord);generation++;renderImage();};
$('show-constructed').onclick=()=>choosePattern('constructed');
$('show-alternating').onclick=()=>choosePattern('alternating');
$('try-constructed').onclick=()=>{choosePattern('constructed');$('show-constructed').focus();};
$('try-alternating').onclick=()=>{choosePattern('alternating');$('show-alternating').focus();};
$('z-layer').oninput=()=>{zLayer=Number($('z-layer').value);renderVolume();};
$('previous-layer').onclick=()=>{zLayer=mod(zLayer-1,m.N);renderVolume();};
$('next-layer').onclick=()=>{zLayer=mod(zLayer+1,m.N);renderVolume();};
load();
