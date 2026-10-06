"""Small, bounded reference construction; no exhaustive mask/image search.

Run this file for twelve fixed smoke cases. They test the implementation,
not the universal theorem proved in research-note.tex. No third-party code.
"""
from itertools import product
import json
from pathlib import Path


def construct(representatives, max_period=256, max_samples=8192):
    a = [tuple(v) for v in representatives]
    if not a or not a[0]:
        raise ValueError("A nonempty mask in positive dimension is required")
    d = len(a[0])
    if any(len(v) != d or not any(v) or
           any(type(z) is not int for z in v) for v in a):
        raise ValueError("Offsets must be nonzero integer vectors")
    signed = {w for v in a for w in (v, tuple(-z for z in v))}
    if len(signed) != 2 * len(a):
        raise ValueError("Offsets must be distinct up to sign")
    M = max(abs(z) for v in a for z in v)
    B = 2 * M + 1
    coefficients = [B ** j for j in range(d)]
    values = [sum(z * b for z, b in zip(v, coefficients)) for v in a]
    if 0 in values or len(set(map(abs, values))) != len(a):
        raise AssertionError("Balanced-base injectivity failed")
    p = max(map(abs, values))
    N = 2 * p
    if N > max_period or N * (2 * len(a) + 1) > max_samples:
        raise ValueError("Reference construction budget exceeded")
    q = [z for z in values if abs(z) != p]
    m = len(q)
    y = [1] * p + [-1] * p

    def crossing(t):
        return sum(y[t] != y[(t + s) % N] for z in q for s in (z, -z))

    def potential():
        return sum(y[t] != y[(t + z) % N] for z in q for t in range(N))

    steps = []
    while True:
        bad = next((t for t in range(p) if crossing(t) < m), None)
        if bad is None:
            break
        before = potential()
        c = crossing(bad)
        y[bad] *= -1
        y[bad + p] *= -1
        after = potential()
        if after - before != 4 * (m - c):
            raise AssertionError("Orbit-flip gain mismatch")
        steps.append({"orbit": bad, "before": before, "after": after})
        if len(steps) > p * m // 2:
            raise AssertionError("Flip bound exceeded")

    # Check the original sample sum, separately from the cut calculation.
    local_sums = [y[t] + sum(y[(t + z) % N] + y[(t - z) % N]
                            for z in values) for t in range(N)]
    if not all(y[t] * local_sums[t] < 0 for t in range(N)):
        raise AssertionError("Median did not reverse every sign")
    assert all(y[t + p] == -y[t] for t in range(p))
    assert N <= B ** d - 1
    return {"mask_pairs": a, "coefficients": coefficients,
            "projected_offsets": values, "period": N,
            "period_bound": B ** d - 1, "word": y,
            "flips": steps, "flip_bound": p * m // 2,
            "minimum_opposite_margin": min(-y[t] * local_sums[t]
                                           for t in range(N))}


def check_actual_torus(result, side, max_pixels=4096):
    """Independent direct coordinate-neighborhood updates, including time two."""
    a = result["mask_pairs"]
    d = len(a[0])
    if side ** d > max_pixels or side % result["period"]:
        raise ValueError("Use a small torus with side a multiple of the period")
    W = [(0,) * d] + [w for v in a for w in (v, tuple(-z for z in v))]
    if len({tuple(z % side for z in v) for v in W}) != len(W):
        raise ValueError("This direct-torus check requires distinct mask samples")
    vertices = list(product(range(side), repeat=d))
    b, y, N = result["coefficients"], result["word"], result["period"]
    x = {v: y[sum(z * c for z, c in zip(v, b)) % N] for v in vertices}

    def median(image):
        out = {}
        for v in vertices:
            samples = sorted(image[tuple((z + w) % side for z, w in zip(v, a))]
                             for a in W)
            out[v] = samples[len(samples) // 2]
        return out

    first = median(x)
    assert all(first[v] == -x[v] for v in vertices)
    assert median(first) == x
    return len(vertices)


def main():
    cases = [
        [(1,)], [(2,)], [(1,), (2,)], [(2,), (4,)],
        [(1,), (2,), (3,)], [(1,), (3,), (4,)],
        [(1,), (2,), (4,)], [(1, 0), (0, 1)],
        [(1, 0), (0, 1), (1, 1), (1, -1)],
        [(2, -1), (1, 2), (1, -1)],
        [(1, 0, 0), (0, 1, 0), (0, 0, 1)],
        [(2, -1, 0), (1, 0, -1), (0, 1, 1), (1, 1, 1)],
    ]
    results = [construct(a) for a in cases]
    torus_pixels = sum(check_actual_torus(results[i], 2 * results[i]["period"])
                       for i in (2, 7, 8))
    # A one-pixel finite torus is fixed, so "every prescribed size" is false.
    fixed_size_control = sorted([1, 1, 1])[1] == 1
    # The zero-only mask is the identity, not an instance of the theorem.
    identity_control = all(sorted([z])[0] == z for z in (-1, 1))
    report = {"status": "PASS", "kind": "bounded implementation checks only",
              "cases": len(results),
              "projected_states_checked": sum(x["period"] for x in results),
              "direct_torus_pixels": torus_pixels,
              "direct_torus_updates": 2,
              "improving_flips_exercised": sum(len(x["flips"]) for x in results),
              "fixed_size_countercontrol": fixed_size_control,
              "identity_countercontrol": identity_control,
              "lean_compiled": False, "azure_resources_created": False,
              "results": results}
    (Path(__file__).resolve().parents[1] / "evidence" / "small-checks.json").write_text(
        json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "results"}))


if __name__ == "__main__":
    main()
