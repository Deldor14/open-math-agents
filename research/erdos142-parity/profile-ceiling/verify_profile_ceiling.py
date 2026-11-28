"""Replay rational dual certificates for the six-width area ceiling.

Only the Python standard library is needed. The multipliers are in
profile-ceiling.json.xz, relative to this file. No LP solver is used here.
"""
from fractions import Fraction
import json
import lzma
from pathlib import Path


def constraints(d, k):
    m = d // 2
    for i in range(m):
        yield 0, ((i, 1), (m + i, -1))
        yield 1, ((m + i, 2), (i, -2))
    a, b, c, e = (2 * m + n * k for n in range(4))
    for t in range(k):
        yield 0, ((a + t, 1), (b + t, -1))
        yield 0, ((c + t, 1), (e + t, -1))
        for start in (a, c):
            yield 1, ((b + t, 1), (e + t, 1), (start + t, -2))

    # A midpoint on the same translated grid requires matching parity.
    for i in range(m):
        for j in range(i, min(m, 2 * k - i), 2):
            t = (i + j) // 2
            for start in (a, c):
                yield 0, ((m + i, 1), (m + j, 1), (start + t, -1))
            for stop in (b, e):
                yield 1, ((i, -1), (j, -1), (stop + t, 1))

    for i in range(m):
        for j in range(i % 2, min(k, 2 * (k - d // 4) - i), 2):
            t = d // 4 + (i + j) // 2
            for start in (a, c):
                yield 0, ((m + i, 2), (b + j, 1), (start + t, -2))
            for stop in (b, e):
                yield 1, ((i, -2), (c + j, -1), (stop + t, 2))


def check_sample(d, k, scale, sparse):
    assert d > 0 and d % 4 == 0 and 0 <= k <= d // 2 and scale > 0
    m = d // 2
    objective = [-2] * m + [2] * m + ([-1] * k + [1] * k) * 2
    residual = [value * scale for value in objective]
    multipliers = dict(sparse)
    assert len(multipliers) == len(sparse)
    assert all(isinstance(i, int) and i >= 0 and isinstance(v, int) and v > 0
               for i, v in sparse)
    total = 0
    for index, (rhs, entries) in enumerate(constraints(d, k)):
        weight = multipliers.pop(index, 0)
        if weight:
            total += 2 * weight * rhs
            for j, coeff in entries:
                residual[j] -= coeff * weight
    assert not multipliers, "Unknown constraint index"
    # Doubled box endpoints are [-1,1] for lower profiles and [0,2] for upper ones.
    total += sum(abs(r) for r in residual[:2 * m])
    total += sum(max(0, 2 * r) for r in residual[2 * m:])
    return Fraction(total, 4 * d * scale)


def check_file(path):
    with lzma.open(path, "rt", encoding="utf-8") as source:
        certificate = json.load(source)
    target = Fraction(certificate["ceiling"])
    valid = []
    samples = 0
    for grid in certificate["grids"]:
        d, scale = grid["D"], grid["scale"]
        bounds = {int(k): check_sample(d, int(k), scale, rows)
                  for k, rows in grid["certificates"].items()}
        samples += len(bounds)
        for k in sorted(bounds):
            if k + 1 in bounds and max(bounds[k], bounds[k + 1]) <= target:
                valid.append((Fraction(k, d), Fraction(k + 1, d)))
    covered = Fraction(0)
    for left, right in sorted(valid):
        assert left <= covered, f"Uncovered cutoff between {covered} and {left}"
        covered = max(covered, right)
    assert covered == Fraction(1, 2)
    print(f"Checked {samples} rational dual certificates; all cutoffs in [0,1/2] covered.")
    print(f"The full profile area is at most {target} ({float(target):.12f}).")


if __name__ == "__main__":
    check_file(Path(__file__).with_name("profile-ceiling.json.xz"))
