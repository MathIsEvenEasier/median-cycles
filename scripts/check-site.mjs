// Small browser-model checks against the separately generated Python fixtures.
// This is not the proof of the theorem and does not run Lean.
import fs from 'node:fs';
import assert from 'node:assert/strict';
import {setup,construct,crossing,median,latticeValue,comparePatterns,periodTwoObstruction} from '../docs/model.mjs';
const cases=JSON.parse(fs.readFileSync(new URL('../evidence/small-checks.json',import.meta.url))).results;
const extra=JSON.parse(fs.readFileSync(new URL('../evidence/site-examples.json',import.meta.url)));
cases.push(extra.new_mask_fixture);
const spatial=JSON.parse(fs.readFileSync(new URL('../evidence/nontrivial-3d.json',import.meta.url)));
cases.push(spatial.fixture);
for(const test of cases){
  const m=setup(test.mask_pairs), trace=construct(m), word=trace.states.at(-1);
  assert.deepEqual(word,test.word);
  assert.equal(m.N,test.period);
  assert.equal(m.periodBound,test.period_bound);
  assert.equal(m.flipBound,test.flip_bound);
  assert.equal(trace.flips.length,test.flips.length);
  for(const y of trace.states) assert(y.every((v,t)=>v===-y[(t+m.p)%m.N]));
  assert(word.every((_,t)=>crossing(m,word,t)>=m.k));
  assert.deepEqual(median(m,word),word.map(v=>-v));
  assert.deepEqual(median(m,median(m,word)),word);
  trace.flips.forEach((f,i)=>{
    assert.equal(f.t,test.flips[i].orbit);
    assert.equal(f.before,test.flips[i].before);
    assert.equal(f.after,test.flips[i].after);
    assert.equal(f.after-f.before,4*(m.k-f.c));
  });
}
const line=setup([[1],[2],[4]]), spin=word=>word.map(v=>2*v-1);
assert.deepEqual(median(line,spin(extra.alternating)),spin(extra.alternating_after));
assert.deepEqual(median(line,spin(extra.witness)),spin(extra.witness_after));
assert.equal(comparePatterns(spin(extra.witness),spin(extra.alternating)),'different');
const mixed=setup(spatial.fixture.mask_pairs),obstruction=periodTwoObstruction(mixed);
assert.equal(obstruction.locked,true);assert.equal(obstruction.agreeing,7);assert.equal(obstruction.total,13);
assert.equal(comparePatterns(spatial.fixture.word,Array.from({length:26},(_,i)=>i%2?-1:1)),'different');
for(let t=0;t<26;t++) {
  const v=[t,0,0],center=latticeValue(mixed,spatial.fixture.word,v);
  const offsets=[[0,0,0],...mixed.pairs.flatMap(a=>[a,a.map(u=>-u)])];
  const votes=offsets.filter(a=>latticeValue(mixed,spatial.fixture.word,a.map((u,j)=>u+v[j]))!==center).length;
  assert.equal(votes,spatial.opposing_vote_counts[t]);
}
const axes=setup([[1,0,0],[0,1,0],[0,0,1]]),volume=construct(axes).states.at(-1);
const checker=Array.from({length:axes.N},(_,i)=>i%2?-1:1);
assert.equal(comparePatterns(volume,checker),'identical');
assert.equal(comparePatterns(volume,checker.map(v=>-v)),'complement');
// Compare every displayed layer crop to the independent parity formula.
for(let z=0;z<axes.N;z++)for(let y=-2;y<=2;y++)for(let x=-2;x<=2;x++){
  const expected=Math.abs(x+y+z)%2===0?1:-1;
  assert.equal(latticeValue(axes,volume,[x,y,z]),expected);
  for(const a of [[1,0,0],[-1,0,0],[0,1,0],[0,-1,0],[0,0,1],[0,0,-1]]){
    assert.equal(latticeValue(axes,volume,[x+a[0],y+a[1],z+a[2]]),-expected);
  }
}
console.log(`PASS: ${cases.length} Python fixtures; antipodality, cut increments, period and flip bounds, and actual median two-cycles.`);
console.log('PASS: pattern comparisons and 450 voxel neighborhoods against the 3D parity formula.');
