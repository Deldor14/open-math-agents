"""Check the band identities in Q(sqrt(2)) and exercise the measure bounds on cell unions."""
import argparse
import sys
from fractions import Fraction
from pathlib import Path


def geometry(module_dir):
    sys.path.insert(0, str(module_dir))
    from verifica_parametro import Cell, F, G, J, R, Surd, V, ell, half, q, rr

    zero = Surd(0)
    quarter = Fraction(1, 4)
    slope_r, slope_l = q * (1 - R), q * R
    delta = (F - J) / 2
    lower_min = half - slope_l
    assert zero < J / 2 < J < F < V < G < quarter < R < half
    assert delta == Surd(quarter, -Fraction(1, 6))
    assert lower_min == q * J / 2 == q * (G - V)
    assert quarter + J < V + G - delta < 2 * G - delta < R

    def width(u):
        if u >= R:
            return zero
        upper = (Cell(zero, zero, sign).edges(half + u) for sign in ("+", "-"))
        return sum((right - left for left, right in upper), zero)

    bands = [(zero, J, quarter, zero, J), (V, G, G - delta, J / 2, J)]
    for lo, hi, shift, xleft, xright in bands:
        for u, mapped in [(lo, xleft), (hi, xright)]:
            v = u + shift
            x = 2 * v - half - u
            assert x == mapped and zero <= x < R and G < v <= R
            assert 2 * rr(v) == slope_r * (half + u) + rr(x)
            assert 1 - 2 * ell(v) == 1 - (ell(u) + slope_l / 2) - ell(x)
            plus = half - ell(u) - min(half - ell(u), slope_r * (half + u))
            minus = half - rr(u) - min(half - rr(u), ell(u) + slope_l / 2)
            assert plus == q * max(zero, F - u)
            assert minus == q * max(zero, G - u)
            target = 1 - 2 * (rr(v) + ell(v))
            assert plus + minus <= target == width(v)
            if lo == zero:
                assert target == plus + minus
                assert half - width(u) == q * (J - u) / 2 <= lower_min
            else:
                assert plus == zero and minus <= lower_min
                assert 2 * minus + 2 * q * delta == target
    for u in (J, F, V):
        assert width(u) == half
    knots = [zero, J / 2, J, V, half]
    weights = []
    for lo, hi in zip(knots, knots[1:]):
        s = (lo + hi) / 2
        degree = 2 * int(s < J or V < s) - 1
        for _, _, _, a, b in bands:
            degree += int(a < s < b)
        weights.append(degree)
    assert weights == [2, 3, -1, 1]
    print("Both affine maps, disjoint targets, endpoint budgets and four weights verified.")


def cell_subsets(n):
    for mask in range(1 << n):
        yield {j for j in range(n) if mask & (1 << j)}


def double_sums():
    count = 0
    for n in range(1, 12):
        for kept in cell_subsets(n):
            # The sum of two unit cells covers two whole cells up to endpoints.
            sums = {i + j + k for i in kept for j in kept for k in (0, 1)}
            missing = n - len(kept)
            assert 2 * n - len(sums) <= 2 * missing
            if kept:
                assert min(kept) + n - 1 - max(kept) <= missing
            count += 1
    print(f"{count} lower-row cell unions passed the sumset and endpoint checks.")


def clipping():
    count = 0
    for p in range(5):
        for m in range(5):
            for slack in range(3):
                size = p + m + slack
                window = set(range(size))
                for left in cell_subsets(p):
                    for right_cells in cell_subsets(m):
                        right = {size - m + i for i in right_cells}
                        for dleft in range(4):
                            for dright in range(4):
                                moved_left = {i - dleft for i in left} & window
                                moved_right = {i + dright for i in right} & window
                                assert moved_left.isdisjoint(moved_right)
                                lost = len(left) + len(right) - len(moved_left | moved_right)
                                assert lost <= dleft + dright
                                count += 1
    print(f"{count} ordered pairs of translated cell unions passed the clipping check.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("geometry", type=Path,
                        help="directory containing the published verifica_parametro.py and verifica_poligono.py")
    geometry(parser.parse_args().geometry.resolve())
    double_sums()
    clipping()
