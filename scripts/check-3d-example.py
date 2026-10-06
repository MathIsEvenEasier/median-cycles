"""Bounded website check: 26 phases and 256 binary blocks; no Lean build."""
from itertools import product
from pathlib import Path
import json
from construct import construct

pairs = [(1, 0, 0), (0, 1, 0), (-2, -2, 1),
         (2, 0, 0), (0, 2, 0), (2, -2, 0)]
fixture = construct(pairs)
mask = [(0, 0, 0)] + [w for a in pairs for w in (a, tuple(-v for v in a))]
word = fixture['word']
N = fixture['period']


def add(a, b):
    return tuple(u + v for u, v in zip(a, b))


def value(v):
    return word[(v[0] + 5 * v[1] + 25 * v[2]) % N]


def update(image, v):
    return sorted(image(add(v, a)) for a in mask)[len(mask) // 2]


# Actual coordinate neighborhoods, using sorting rather than the JS spin sum.
opposing = []
for t in range(N):
    v = (t, 0, 0)
    assert update(value, v) == -value(v)
    assert update(lambda w: update(value, w), v) == value(v)
    opposing.append(sum(value(add(v, a)) != value(v) for a in mask))
assert N == 26 and len(fixture['flips']) == 7
assert min(opposing) == 7 and max(opposing) == 10
assert all(any(word[(t + k) % N] != word[t] for t in range(N))
           for k in range(1, N))

# Every possible 2x2x2 binary block remains fixed under this mask.
vertices = list(product(range(2), repeat=3))
for bits in range(256):
    def block(v):
        i = (v[0] % 2) + 2 * (v[1] % 2) + 4 * (v[2] % 2)
        return 1 if bits & (1 << i) else -1
    assert all(update(block, v) == block(v) for v in vertices)

report = {'status': 'PASS', 'kind': 'bounded example checks, not the general proof',
          'fixture': fixture, 'phases_checked': N, 'direct_coordinate_updates': 2,
          'period_two_blocks_checked': 256, 'all_period_two_blocks_fixed': True,
          'opposing_vote_counts': opposing}
path = Path(__file__).resolve().parents[1] / 'evidence' / 'nontrivial-3d.json'
path.write_text(json.dumps(report, indent=2) + '\n')
print('PASS: 26 phases flip and return; all 256 period-two blocks stay fixed; '
      '7 construction flips; 7–10 opposing votes out of 13.')
