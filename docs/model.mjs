export const presets = [
  {name: 'Offsets 1, 2, 4 · 1D', pairs: [[1],[2],[4]]},
  {name: 'Mixed distances · 2D', pairs: [[1,0],[2,0],[0,2]]},
  {name: 'Cross · 2D', pairs: [[1,0],[0,1]]},
  {name: 'Full 3 × 3 · 2D', pairs: [[1,0],[0,1],[1,1],[1,-1]]},
  {name: 'Skew mask · 2D', pairs: [[2,-1],[1,2],[1,-1]]},
  {name: 'Axis neighbors · 3D', pairs: [[1,0,0],[0,1,0],[0,0,1]]}
];
export const mod = (a,n) => ((a%n)+n)%n;
export function latticeValue(m,word,coordinates) {
  return word[mod(coordinates.reduce((s,v,j)=>s+v*m.coefficients[j],0),m.N)];
}
export function comparePatterns(a,b) {
  if(a.every((v,t)=>v===b[t])) return 'identical';
  if(a.every((v,t)=>v===-b[t])) return 'complement';
  return 'different';
}
export function setup(pairs) {
  const d=pairs[0].length, r=pairs.length, M=Math.max(...pairs.flat().map(Math.abs)), B=2*M+1;
  const coefficients=Array.from({length:d},(_,j)=>B**j);
  const q=pairs.map(a=>a.reduce((s,v,j)=>s+v*coefficients[j],0));
  const p=Math.max(...q.map(Math.abs)), N=2*p;
  if (N>256 || N*r>4096) throw Error('Demonstration size exceeded');
  const remaining=q.filter(v=>Math.abs(v)!==p), k=r-1;
  return {pairs,d,r,M,B,coefficients,q,p,N,remaining,k,periodBound:B**d-1,flipBound:Math.floor(p*k/2)};
}
export function crossing(m,y,t) {return m.remaining.reduce((s,q)=>s+Number(y[t]!==y[mod(t+q,m.N)])+Number(y[t]!==y[mod(t-q,m.N)]),0);}
export function cut(m,y) {return m.remaining.reduce((s,q)=>s+y.reduce((n,v,t)=>n+Number(v!==y[mod(t+q,m.N)]),0),0);}
export function samples(m,y,t) {return [{offset:0,value:y[t],index:t,extreme:false},...m.q.flatMap(q=>[q,-q].map(a=>({offset:a,value:y[mod(t+a,m.N)],index:mod(t+a,m.N),extreme:Math.abs(a)===m.p})))];}
export function median(m,y) {return y.map((_,t)=>Math.sign(samples(m,y,t).reduce((s,v)=>s+v.value,0)));}
export function construct(m) {
  let y=Array.from({length:m.N},(_,t)=>t<m.p?1:-1);
  const states=[y.slice()], flips=[];
  for (;;) {
    const t=Array.from({length:m.p},(_,i)=>i).find(t=>crossing(m,y,t)<m.k);
    if(t===undefined) break;
    const c=crossing(m,y,t), before=cut(m,y);
    y=y.slice(); y[t]*=-1; y[t+m.p]*=-1;
    const after=cut(m,y);
    if(after-before!==4*(m.k-c)) throw Error('Flip identity failed');
    flips.push({t,c,before,after}); states.push(y);
    if(flips.length>m.flipBound) throw Error('Flip bound failed');
  }
  if(!median(m,y).every((v,t)=>v===-y[t])) throw Error('Median certificate failed');
  return {states,flips};
}
