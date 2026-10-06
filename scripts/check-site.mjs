// Small browser-model checks against the separately generated Python fixtures.
// This is not the proof of the theorem and does not run Lean.
import fs from 'node:fs';
import assert from 'node:assert/strict';
import {setup,construct,crossing,median} from '../docs/model.mjs';
const cases=JSON.parse(fs.readFileSync(new URL('../evidence/small-checks.json',import.meta.url))).results;
const extra=JSON.parse(fs.readFileSync(new URL('../evidence/site-examples.json',import.meta.url)));
cases.push(extra.new_mask_fixture);
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
console.log(`PASS: ${cases.length} Python fixtures; antipodality, cut increments, period and flip bounds, and actual median two-cycles.`);
