"""Exact checks of the finite comparisons in Perforations.md (Python 3)."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import sys

sys.path.insert(0, str(Path(sys.argv[1]).resolve()))
from verifica_parametro import Cell, J, Surd, half, q


def check_pruning():
    size = 9
    stencils = []
    for step in (1, 2, 4):
        for i in range(step, size - step):
            mask = (1 << (i - step)) | (1 << i) | (1 << (i + step))
            stencils.append((i, step, mask))
    admissible = 0
    strictly_pruned = 0
    for entries in product((0, 1), repeat=size):
        differences = {(i, s): entries[i-s] + entries[i+s] - 2*entries[i]
                       for i, s, _ in stencils}
        for present in range(1 << size):
            full = {(i, s) for i, s, mask in stencils if present & mask == mask}
            if (4, 4) not in full or any(differences[node] < 0 for node in full):
                continue
            admissible += 1
            kept = {}
            for i, s, _ in stencils:
                if s == 1:
                    kept[i, s] = differences[i, s] if (i, s) in full else 0
                else:
                    t = s // 2
                    children = ((i-t, t), (i, t), (i+t, t))
                    kept[i, s] = sum(weight * kept[ch] for weight, ch in
                                     zip((1, 2, 1), children)) if all(
                                         ch in full for ch in children) else 0
                if (i, s) in full:
                    assert 0 <= kept[i, s] <= differences[i, s]
            strictly_pruned += kept[4, 4] < differences[4, 4]
    assert strictly_pruned and admissible > strictly_pruned
    print(f"{admissible} admissible binary height/mask pairs; "
          f"{strictly_pruned} strictly pruned root sums.")


def check_interpolation():
    tests = 0
    for denom in range(2, 38):
        for numerator in range(denom):
            x = Q(numerator, denom)
            remainder = x
            weighted_sum = Q(0)
            for depth in range(1, 15):
                endpoint = int(2 * remainder)
                remainder = 2 * remainder - endpoint
                weighted_sum += Q(endpoint, 2**depth)
                assert weighted_sum + remainder / 2**depth == x
                # Every convex quadratic with affine term obeys the Jensen step.
                f = lambda y: y*y - 3*y + 2
                previous = (endpoint + remainder) / Q(2)
                assert f(previous) <= (f(endpoint) + f(remainder)) / 2
                tests += 1
    print(f"{tests} exact dyadic interpolation identities and Jensen steps.")


def edges(u):
    lower_plus, upper_plus = Cell(None, None, '+').edges(half + u)
    lower_minus, upper_minus = Cell(None, None, '-').edges(half + u)
    return (2*lower_plus-half, 2*lower_minus+half,
            2*upper_plus-half, 2*upper_minus+half)


def check_mesh():
    comparisons = 0
    for i in range(1, 16):
        u = J*i/16
        a, p, c, d = edges(u)
        alpha = (2*a + 1 - a - p) / (c + d - a - p)
        assert 0 < alpha < 1
        x = a + alpha*(c-a)
        z = p + alpha*(d-p)
        for exponent in (14, 18):
            r = Q(1, 2**exponent)
            step = 2*r/q
            aminus, _, _, _ = edges(u-step)
            _, pplus, _, _ = edges(u+step)
            for tau in (-r/3, Q(0), r/3):
                first, last = a+r+tau, d-r+tau
                assert (aminus + r + tau + pplus + r + tau)/2 + half == last
                assert (x+r+tau + z+r+tau)/2 - half == first
                assert a < x+r+tau < c and p < z+r+tau < d
                grid = [first + (last-first)*Q(j, 32) for j in range(33)]
                for left, right in zip(grid, grid[2:]):
                    assert a < left <= right < c or p < left <= right < d
                    comparisons += 1
    print(f"{comparisons} exact three-node sheet inclusions; "
          "both mixed midpoint identities at 90 translated meshes.")


if __name__ == '__main__':
    check_pruning()
    check_interpolation()
    check_mesh()
