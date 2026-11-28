"""Exact checks for the circle energy and the guarded-arc integral."""
from fractions import Fraction as F
from functools import cache
from itertools import product


def edges(n, k):
    return [sum(1 << (x + i * d) for i in range(k))
            for d in range(1, (n - 1) // (k - 1) + 1)
            for x in range(n - (k - 1) * d)]


def free(mask, forbidden):
    return all(mask & e != e for e in forbidden)


def test_cubic_sampling():
    checks = 0
    for prime in (3, 5, 7):
        sizes = []
        for n in range(1, prime + 1):
            triples = edges(n, 3)
            rank = max(bin(s).count("1") for s in range(1 << n) if free(s, triples))
            sizes.append((n, rank, len(triples)))
        for f in product(range(3), repeat=prime):
            mass = sum(f)
            moment = sum(x**3 for x in f)
            correlation = sum(f[x] * f[(x + d) % prime] * f[(x + 2*d) % prime]
                              for x in range(prime) for d in range(prime))
            for n, rank, count in sizes:
                assert 4*n**3*mass**3 <= rank**2*(
                    4*n*prime**2*moment + 27*count*prime*correlation)
                checks += 1
    return checks


def polygon_cut(vertices, signed):
    """Intersect a convex rational polygon with signed(point) >= 0."""
    out = []
    for p, q in zip(vertices, vertices[1:] + vertices[:1]):
        a, b = signed(p), signed(q)
        if a >= 0:
            out.append(p)
        if a*b < 0:
            t = a / (a-b)
            out.append(tuple(x+t*(y-x) for x, y in zip(p, q)))
    return out


def area(vertices):
    return abs(sum((x*v-y*u for (x,y),(u,v) in
                    zip(vertices, vertices[1:] + vertices[:1])), F(0))) / 2


@cache
def floor_patterns(k):
    """Partition the two continuous fractional starting positions (u,v)."""
    square = [(F(0),F(0)), (F(1),F(0)), (F(1),F(1)), (F(0),F(1))]
    regions = [((), square)]
    for j in range(2, k):
        refined = []
        for prefix, vertices in regions:
            for h in range(1-j, j):
                p = polygon_cut(vertices, lambda z: (1-j)*z[0]+j*z[1]-h)
                p = polygon_cut(p, lambda z: h+1-((1-j)*z[0]+j*z[1]))
                if area(p):
                    refined.append((prefix+(h,), p))
        regions = refined
    result = [(t, area(p)) for t, p in regions]
    assert sum(m for _, m in result) == 1
    return result


def test_arc_integrals():
    checks = 0
    for k in (3, 4, 5):
        patterns = floor_patterns(k)
        for n in range(1, 9):
            q = 4*n
            forbidden = edges(n, k)
            for s in range(1, 1 << n):
                if not free(s, forbidden):
                    continue
                occupied = {2*j for j in range(n) if s >> j & 1}
                integral_times_q_squared = F(0)
                for x, y in product(occupied, repeat=2):
                    for corrections, weight in patterns:
                        if all(((1-j)*x+j*y+h) % q in occupied
                               for j,h in enumerate(corrections, start=2)):
                            integral_times_q_squared += weight
                assert integral_times_q_squared == F(len(occupied), k-1)
                checks += 1
    return checks


def test_fourier_program():
    """Constant coefficients yield exact circle integrals for integer polynomials."""
    def multiply(a, b):
        out = {}
        for i,x in a.items():
            for j,y in b.items():
                out[i+j] = out.get(i+j, 0) + x*y
        return out

    checked = 0
    for z in product(range(-2,3), repeat=4):
        if not any(z):
            continue
        a = multiply(dict(enumerate(z)), {-i:v for i,v in enumerate(z)})
        moment = multiply(multiply(a, a), a)[0]
        corr = sum(v*v*a.get(-2*i, 0) for i,v in a.items())
        # Expand all monomials with exponent zero in both x and d independently.
        second = sum(u*v*w for i,u in a.items() for j,v in a.items()
                     for h,w in a.items() if i+j+h == 0 and j+2*h == 0)
        assert corr == second and moment >= 0 and corr >= 0
        checked += 1
    return checked


if __name__ == '__main__':
    print('weighted cyclic inequalities:', test_cubic_sampling())
    print('exact circle integrals for arc unions:', test_arc_integrals())
    print('Fourier polynomial identities:', test_fourier_program())
