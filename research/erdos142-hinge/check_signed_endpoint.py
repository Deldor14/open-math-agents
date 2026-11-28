"""Exact arithmetic checks on the signed rational benchmark, independent of Lean."""
from fractions import Fraction as F

p, q, w = F(69, 56), F(25, 28), F(3, 28)
h = (1-w)/(p+q)
half, quarter = F(1, 2), F(1, 4)


def intervals(s):
    if 0 < s < half:
        return [(-p*s/2, min(w+q*s, 1-p*s)/2, 0)]
    t = s-half
    if not 0 < t < h:
        return []
    upper = 1-2*p*t
    base = 2*w+q-1+2*q*t
    pos = min(upper, base)
    left = min(1-2*w-2*q*t, (2-upper-base)/2)
    minus = min(left, p-1+2*p*t)
    return [(quarter-left/4, quarter+pos/4, 1), (-quarter-minus/4, -quarter+upper/4, 0)]


def verify_grid(n, eta):
    coefficient = 12/eta**2
    assert coefficient.denominator == 1
    coefficient = int(coefficient)
    points = {}
    for s in range(n):
        if abs(F(s, n)-half) <= eta:
            continue
        for lo, hi, label in intervals(F(s, n)):
            for a in range(-n//2, n//2):
                if lo+eta < F(a,n) < hi-eta:
                    u = a-label*(n//2)
                    points[s,a % n] = (s, a, u, coefficient*s*s+4*u*u)
    triples = 0
    for (ys, ya), y in points.items():
        for (xs, xa), x in points.items():
            z = points.get(((2*ys-xs) % n, (2*ya-xa) % n))
            if z is None:
                continue
            assert x[0]+z[0]-2*y[0] in (0,n)
            assert 4*(x[3]+z[3]-2*y[3]) >= coefficient*(x[0]-z[0])**2+4*(x[1]-z[1])**2
            triples += 1
    print(f'grid={n}, eta={eta}, points={len(points)}, ordered triples={triples}')


def verify_half_turn(tau):
    t = F(1,16)
    pos = intervals(half+t+tau)[0]
    neg = intervals(half+t-tau)[1]
    mid = intervals(half+t)[0]
    e = (p+q)*tau/8
    ax, az, ay = pos[1]-e, neg[1]-e, mid[0]+e
    assert pos[0] < ax < pos[1] and neg[0] < az < neg[1] and mid[0] < ay < mid[1]
    ux, uz, uy = ax-half, az, ay-half
    assert ax+az == 2*ay and ux+uz-2*uy == half
    assert ux**2+uz**2-2*uy**2 < 0


if __name__ == '__main__':
    for size in (24, 36, 48, 60):
        verify_grid(size, F(1, 100))
    for k in range(2, 12):
        verify_half_turn(F(1, 10**k))
    print('Verified 10 exact untrimmed positive half-turn witnesses.')
