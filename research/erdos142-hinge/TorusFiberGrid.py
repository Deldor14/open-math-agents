"""Exact verifier for the four-cell, two-arc problem in TorusFibers.md (standard library)."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json

HALF = Q(1, 2)
LOWER = (Q(0), Q(50, 119), HALF)
UPPER = (Q(0), Q(12, 119), Q(19, 119), Q(25, 119), Q(50, 119))
OPTIMUM = Q(579, 1904)
MODES = "ABDF"
HERE = Path(__file__).resolve().parent


def model(pattern):
    """Return trapezoid weights and rows (rhs, [(coefficient index, multiplier), ...])."""
    lower_count = len(LOWER) - 1
    cells = list(zip(LOWER, LOWER[1:])) + list(zip(UPPER, UPPER[1:]))
    indices, weights, rows = {}, [], []

    for i, (left, right) in enumerate(cells):
        lower = i < lower_count
        for field in ("LW" if lower else "PUVM"):
            indices[i, field] = len(weights)
            weights.extend([(right - left) / (4 if lower else 8)] * 2)

    def value(i, field, point, coefficient=1):
        left, right = cells[i]
        t = (point - left) / (right - left)
        start = indices[i, field]
        return [(start, coefficient * (1 - t)), (start + 1, coefficient * t)]

    for i, (left, right) in enumerate(cells):
        for point in (left, right):
            def v(field, coefficient=1):
                return value(i, field, point, coefficient)
            if i < lower_count:
                rows.extend([(1, v("L") + v("W")), (0, v("L", -1) + v("W", -1))])
                continue
            mode = pattern[i - lower_count]
            if mode == "A":
                rows.extend((2, v("P") + v("U") + v(f, 2)) for f in "VM")
            elif mode == "B":
                rows.extend((2, v("V") + v("M") + v(f, 2)) for f in "PU")
            elif mode in "DF":
                f, g = "PM" if mode == "D" else "UV"
                rows.append((0, v(f) + v(g)))
            elif mode != "*":
                raise ValueError(mode)
            for f, g in ("PV", "MU"):
                rows.append((0, v(f, -1) + v(g, -1)))

    for i, (a0, a1) in enumerate(cells[:lower_count]):
        for j in range(i, len(cells)):
            b0, b1 = cells[j]
            shift = Q(0) if j < lower_count else Q(1, 4)
            for k in range(lower_count, len(cells)):
                t0, t1 = cells[k]
                lo, hi = 2 * (t0 - shift), 2 * (t1 - shift)
                if a0 + b0 >= hi or a1 + b1 <= lo:
                    continue
                vertices = set(product((a0, a1), (b0, b1)))
                vertices.update((a, s - a) for a in (a0, a1) for s in (lo, hi))
                vertices.update((s - b, b) for b in (b0, b1) for s in (lo, hi))
                for a, b in sorted(vertices):
                    if not (a0 <= a <= a1 and b0 <= b <= b1 and lo <= a + b <= hi):
                        continue
                    t = shift + (a + b) / 2
                    if j < lower_count:
                        for f, g in ("LP", "LU", "WV", "WM"):
                            rows.append((1, value(i, f, a) + value(j, f, b) + value(k, g, t)))
                    else:
                        for f, g, targets in (("W", "P", "VM"), ("L", "M", "PU")):
                            for target in targets:
                                rows.append((1, value(i, f, a, 2) + value(j, g, b) + value(k, target, t, 2)))
    return weights, rows


def reflect(pattern):
    # Physical angular reflection exchanges A and B, leaving the gap alternatives D and F fixed.
    return pattern.translate(str.maketrans("AB", "BA"))


def verify():
    data = json.loads((HERE / "TorusFiberCertificates.json").read_text())
    primal = list(map(Q, data["primal"]))
    objective, rows = model("AAAA")
    assert len(primal) == len(objective) and all(abs(v) <= 1 for v in primal)
    assert all(sum(v * primal[j] for j, v in terms) <= rhs for rhs, terms in rows)
    assert sum(v * w for v, w in zip(primal, objective)) == OPTIMUM
    covered = set()
    for pattern, multipliers in data["dual"].items():
        residual, rows = model(pattern)
        bound = Q(0)
        for index, weight in multipliers:
            y = Q(weight)
            assert y >= 0 and 0 <= index < len(rows)
            rhs, terms = rows[index]
            bound += y * rhs
            for j, v in terms:
                residual[j] -= y * v
        assert bound + sum(abs(v) for v in residual) <= OPTIMUM, pattern
        for case in product(MODES, repeat=4):
            if all(m == "*" or m == c for m, c in zip(pattern, case)):
                label = "".join(case)
                covered.update((label, reflect(label)))
    assert covered == {"".join(case) for case in product(MODES, repeat=4)}
    print(f"{len(covered)} mode assignments, {len(data['dual'])} rational upper certificates, optimum {OPTIMUM}")


if __name__ == "__main__":
    verify()
