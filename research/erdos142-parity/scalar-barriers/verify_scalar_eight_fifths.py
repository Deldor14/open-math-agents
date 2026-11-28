"""Rational verification over all real arguments for ScalarEightFifths.lean."""

from fractions import Fraction as Q
from itertools import combinations

KNOTS = ((0,0), (2,2), (3,2), (5,4), (8,4), (15,8), (16,8))
END = KNOTS[-1][0]


def shape(x):
    for (a, u), (b, v) in zip(KNOTS, KNOTS[1:]):
        if x <= b:
            return u + (x - a) * Q(v-u, b-a)
    return x / 2


def corners(factor):
    # Each line is given as ax+by=c. Include the x=y boundary.
    lines = {(1, -1, 0)}
    for t, _ in KNOTS:
        lines.update(((1, 0, t), (0, 1, t), (1, factor, t)))
    points = set()
    for (a,b,c), (h,j,k) in combinations(sorted(lines), 2):
        det = a*j - h*b
        if det:
            x, y = Q(c*j-k*b,det), Q(a*k-h*c,det)
            if 0 <= x <= y <= END:
                points.add((x,y))
    return points


def verify():
    # Monotonicity and both bounds extend from vertices by affinity.
    for (a,u), (b,v) in zip(KNOTS, KNOTS[1:]):
        assert a < b and u <= v
    assert all(Q(x,2) <= y <= x for x,y in KNOTS)
    assert shape(Q(5)) == shape(Q(8)) == 4
    assert shape(Q(END)) == Q(END,2)
    for p in (1,2):
        pts = corners(p)
        # Each difference is affine on each cell, so min occurs at a corner.
        for x,y in pts:
            delta = shape(x)+shape(y)-shape(x+p*y)
            assert delta >= 0 if p == 1 else delta <= 0, (p,x,y,delta)
        print(f"p={p}: {len(pts)} exact rational vertices verified")
    # At y >= END, holding x in [0,END] fixed, the subadditivity slack
    # stays constant and the gluing slack increases by (y-END)/2.
    # For END <= x <= y, shape is everywhere the linear function t/2.


if __name__ == "__main__":
    verify()
