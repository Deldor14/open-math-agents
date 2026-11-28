"""Exact area and separation checks for the upper-sheet extension of the six-width block.

Python 3.9+, no dependencies. Six-width profiles: CubeJerry, b19425c1cd70,
round2. The separating-axis audit below uses the original lifted coordinates.
"""
from fractions import Fraction as F
from itertools import combinations_with_replacement, product

HALF = F(1, 2)
QUARTER = F(1, 4)


def det(p, q, r):
    return (q[0]-p[0])*(r[1]-p[1])-(q[1]-p[1])*(r[0]-p[0])


def hull(points):
    ordered = sorted(set(points))

    def chain(items):
        vertices = []
        for v in items:
            while len(vertices) >= 2 and det(vertices[-2], vertices[-1], v) <= 0:
                vertices.pop()
            vertices.append(v)
        return vertices[:-1]

    return chain(ordered) + chain(reversed(ordered))


def area(polygon):
    following = polygon[1:] + polygon[:1]
    return abs(sum(x*v-y*u for (x, y), (u, v) in zip(polygon, following))) / 2


def have_disjoint_interiors(polygon, other):
    for p, q in zip(polygon, polygon[1:] + polygon[:1]):
        if all(det(p, q, r) <= 0 for r in other):
            return True
    for p, q in zip(other, other[1:] + other[:1]):
        if all(det(p, q, r) <= 0 for r in polygon):
            return True
    return False


def vertices(xs, zs, totals):
    return ({(x, z) for x in xs for z in zs}
            | {(x, total-x) for x in xs for total in totals}
            | {(total-z, z) for z in zs for total in totals})


def audit(p, q, w):
    b, h = 1/(2*p), (1-w)/(p+q)
    cutoff, top = HALF+b, HALF+h
    assert 0 < 2*cutoff-top < cutoff < top < 2*top-cutoff < 1
    lower_cuts = [F(0), h, HALF]
    upper_cuts = [F(0), (2-p-w-q/2)/(p+q), (q/2-w)/(p+q),
                  (1-w-q/2)/(p+q), b]
    assert upper_cuts == sorted(set(upper_cuts))
    assert upper_cuts[-2] < QUARTER < b < h < HALF

    def lower(s):
        return p*s, min(w+q*s, 1-p*s)

    def upper(t):
        u = 1-2*p*t
        v = min(1-2*w-2*q*t, 1-w-q/2+(p-q)*t)
        return min(u, 2*w+q-1+2*q*t), u, v, min(v, p-1+2*p*t)

    lo, pos, neg = [], [], []
    for s in lower_cuts:
        l, z = lower(s)
        assert 0 <= l <= 1 and 0 <= z <= 1 and l+z <= 1
        lo.extend([(s, -l/2), (s, z/2)])
    for t in upper_cuts:
        pos_w, u, v, m = upper(t)
        assert all(0 <= z <= 1 for z in (pos_w, u, v, m))
        assert pos_w+u+2*max(v, m) <= 2
        pos.extend([(HALF+t, QUARTER-v/4), (HALF+t, QUARTER+pos_w/4)])
        neg.extend([(HALF+t, -QUARTER-m/4), (HALF+t, -QUARTER+u/4)])

    # Each affine region has vertical, horizontal, or slope-minus-one
    # boundary lines. Its extrema occur at these intersections.
    for x, z in vertices(lower_cuts, lower_cuts, [2*t for t in upper_cuts]):
        t = (x+z)/2
        if 0 <= x <= HALF and 0 <= z <= HALF and 0 <= t <= b:
            lx, wx = lower(x)
            lz, wz = lower(z)
            pt, ut, vt, mt = upper(t)
            assert lx+lz+max(pt, ut) <= 1
            assert wx+wz+max(vt, mt) <= 1
    for x, z in vertices(lower_cuts, upper_cuts, [2*t-HALF for t in upper_cuts]):
        t = QUARTER+(x+z)/2
        if 0 <= x <= HALF and 0 <= z <= b and 0 <= t <= b:
            lx, wx = lower(x)
            pz, _, _, mz = upper(z)
            pt, ut, vt, mt = upper(t)
            assert pz+2*wx+2*max(vt, mt) <= 1
            assert mz+2*lx+2*max(pt, ut) <= 1

    parts = list(map(hull, [lo, pos, neg]))
    for x, z in [(0, 1), (0, 2), (1, 2)]:
        assert have_disjoint_interiors(parts[x], parts[z])
    triangle = hull([(2*b, HALF), (2*b, w+q*b), (2*h, 1-p*h)])
    assert all(0 <= u <= 1 and 0 < v <= HALF for u, v in triangle)
    assert all(0 <= u <= 1 and -HALF <= v <= HALF
               for shape in parts for u, v in shape)
    checks = 0
    for left, right in combinations_with_replacement(parts, 2):
        pair_sum = hull([(x+z, a+c) for x, a in left for z, c in right])
        for i, j in product(range(-2, 3), repeat=2):
            translated = [(s+i, a+j) for s, a in pair_sum]
            assert have_disjoint_interiors(translated, triangle)
            checks += 1

    rho_old = sum(map(area, parts))
    hole = area(triangle)
    assert hole == (p+q)*(h-b)**2
    return rho_old, hole, rho_old+hole/2, checks


if __name__ == "__main__":
    cases = [
        (F(6,5), F(9,10), F(7,60), F(613,2016)),
        (F(75,61), F(33,37), F(1465,13542), F(8302055,27300672)),
        (F(2416,1965), F(1121,1257), F(178159,1646670),
         F(6996681280867,23008050468240)),
    ]
    for p, q, w, expected in cases:
        old, hole, rho, tests = audit(p, q, w)
        assert rho == expected
        print(f"p={p}, q={q}, w={w}, base={old}, hole={hole}, rho={rho}, "
              f"rho decimal={float(rho):.12f}, separations={tests}")
