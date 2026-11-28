"""Independently certify the table by enumerating rational slopes and intercepts."""
from fractions import Fraction
from math import ceil, floor
from pathlib import Path


def feasible(n, width):
    # At a vertex of the width function two residuals coincide, unless the
    # slope is an endpoint. Scale by the denominator to make residuals integral.
    slopes = {Fraction(a, d) for d in range(1, max(3, n))
              for a in range(d // 2 + 1)}
    for slope in slopes:
        a, d = slope.numerator, slope.denominator
        span = floor(d * width)
        for base in range(-span, 1):
            choices = [range(-(-(i * a + base) // d),
                              (i * a + base + span) // d + 1) for i in range(n)]
            heights = [0]

            def fill():
                i = len(heights)
                if i == n:
                    return True
                forbidden = {2 * heights[i - k] - heights[i - 2 * k]
                             for k in range(1, i // 2 + 1)}
                for h in choices[i]:
                    if h not in forbidden:
                        heights.append(h)
                        if fill():
                            return True
                        heights.pop()
                return False

            if fill():
                return True
    return False


def check(n, width):
    assert feasible(n, width), (n, width)
    if width:
        preceding = max(Fraction(ceil(d * width) - 1, d)
                        for d in range(1, max(3, n)))
        assert not feasible(n, preceding), (n, preceding)


if __name__ == "__main__":
    for line in Path(__file__).with_name("height-strip-values.txt").read_text().splitlines():
        n, width, _, _ = line.split()
        check(int(n), Fraction(width))
        print(f"Verified W({n}) = {width}", flush=True)
