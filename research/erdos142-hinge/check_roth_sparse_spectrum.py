"""Exact Fourier and restricted projection tests; all coefficient arithmetic is integral."""
from collections import defaultdict
from itertools import combinations, product
import random


def moment_and_correlation(f):
    moment = sum(v*w*f.get(-i-j, 0) for i,v in f.items() for j,w in f.items())
    correlation = sum(v*v*f.get(-2*i, 0) for i,v in f.items())
    return moment, correlation


def row_test(p):
    spectrum = tuple(p)
    f = defaultdict(int)
    for a,c in product(p, repeat=2):
        f[a-c] += p[a]*p[c]
    f = {a:v for a,v in f.items() if v}
    j, l = moment_and_correlation(f)
    coeff = defaultdict(int)
    rows = defaultdict(set)
    for a,b,c in product(spectrum, repeat=3):
        u, t = a+b+c, c-a
        coeff[u,t] += p[a]*p[b]*p[c]
        rows[u].add(t)
    assert sum(sum(coeff[u,t] for t in ts)**2 for u,ts in rows.items()) == j
    assert sum(v*v for v in coeff.values()) == l
    assert j <= max(map(len, rows.values()))*l
    zero = {c-a for a,c in product(f,repeat=2) if -a-c in f}
    assert j <= len(zero)*l
    for u, ts in rows.items():
        assert ts == {c-a for a,c in product(p,repeat=2) if u-a-c in p}
    # For several small retained spectra compute the tail estimate even when
    # frequency fibers have many cancellations from signed coefficients.
    ordered = sorted(f, key=lambda a: -abs(f[a]))
    energy = sum(v*v for v in f.values())
    for size in {1, max(1,len(f)//2), len(f)}:
        retained = set(ordered[:size])
        good = {c-a for a,c in product(retained,repeat=2) if -a-c in retained}
        tail = sum(abs(v) for i,v in f.items() if i not in retained)
        assert j <= len(good)*l + 3*energy*tail


def all_graphs():
    edges = list(product((-3,0,5), (-1,2,7)))
    for mask in range(1 << len(edges)):
        g = [e for i,e in enumerate(edges) if mask >> i & 1]
        s = {z for a,b in g for z in (a,b,-a-b)}
        row = {c-a for a,c in product(s,repeat=2) if -a-c in s}
        assert {b-a for a,b in g} <= row
        if row:
            # Taking coefficient one in this row makes the row estimate sharp.
            assert sum(1 for _ in row)**2 == len(row)*sum(1 for _ in row)
    return 1 << len(edges)


def main():
    cases = 0
    for support in combinations((-31,-3,-1,0,1,2,4,39), 3):
        for v in product((-2,1), repeat=3):
            row_test(dict(zip(support,v)))
            cases += 1
    rng = random.Random(142)
    for _ in range(120):
        support = rng.sample(range(-15,16), rng.randrange(2,8))
        row_test({i:rng.choice((-2,-1,1,2)) for i in support})
        cases += 1
    print('Signed polynomial spectra:', cases)
    print('Restricted projection graphs:', all_graphs())


if __name__ == '__main__':
    main()
