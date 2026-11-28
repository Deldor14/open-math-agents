"""Integer checks of the weighted count, random maximum and fingerprint split."""
from fractions import Fraction
from itertools import combinations


def tables(n, k):
    size = 1 << n
    card = [0]*size
    edges = [sum(1 << (x+j*d) for j in range(k))
             for d in range(1, (n-1)//(k-1)+1)
             for x in range(n-(k-1)*d)]
    independent = [all(e & a != e for e in edges) for a in range(size)]
    contained = list(map(int, independent))
    alpha = [0]*size
    for a in range(1, size):
        card[a] = 1+card[a & (a-1)]
        if independent[a]:
            alpha[a] = card[a]
        else:
            edge = next(e for e in edges if e & a == e)
            alpha[a] = max(alpha[a ^ (1 << i)] for i in range(n) if edge >> i & 1)
    # Subset zeta transform counts all contained independent sets.
    for i in range(n):
        bit = 1 << i
        for a in range(size):
            if a & bit:
                contained[a] += contained[a ^ bit]
    assert all((1 << alpha[a]) <= contained[a] for a in range(size))
    return card, independent, contained, alpha


def check_model(n, k, p):
    card, independent, contained, alpha = tables(n, k)
    u, v = p.numerator, p.denominator
    mass = [u**i*(v-u)**(n-i) for i in range(n+1)]
    polynomial = sum(u**c * v**(n-c) for c, good in zip(card, independent) if good)
    direct = sum(mass[c] * value for c, value in zip(card, contained))
    assert direct == polynomial
    mean_numerator = sum(mass[c]*value for c, value in zip(card, alpha))
    if n == -(-(v**(k-1)) // u**(k-1)):
        assert 5*mean_numerator*v >= u*n*v**n
    for h in range(n+1):
        tail = sum(mass[c] for c, value in zip(card, alpha) if value >= h)
        assert (1 << h)*tail <= polynomial
    return len(card)


def check_fingerprints():
    n = 9
    card, free, _, _ = tables(n, 3)
    partitions = 0
    for base in (3, 11, 29, 73, 121):
        # A nonconstant choice of compulsory fingerprint for each input.
        groups = {}
        for a, ok in enumerate(free):
            if ok:
                candidates = a & base
                fingerprint = candidates & -candidates if card[a] % 2 else candidates
                groups.setdefault(fingerprint, []).append(a ^ fingerprint)
        for z in (Fraction(1, 5), Fraction(2, 3), Fraction(1)):
            direct = sum(z**card[i] for i, ok in enumerate(free) if ok)
            split = sum(z**card[f] * sum(z**card[r] for r in rests)
                        for f, rests in groups.items())
            assert direct == split
            for H in (1, 2, 5):
                J = max(card[f] for f in groups)
                assert sum(z**card[f] for f in groups) <= H**J*(1+z/H)**n
                partitions += 1
    return partitions


def check_affine_host():
    prime = 83
    hosts = [(3, 17, 31, 45, 47, 57, 68), (0, 3, 6, 9, 12, 37, 62, 81)]
    count = 0
    for k in (3, 4):
        for host in hosts:
            edges = [edge for edge in combinations(host, k)
                     if all(y-x == edge[1]-edge[0] for x, y in zip(edge, edge[1:]))]
            cover = {e[:2] for e in edges}
            for b in (2, 4, 5):
                card, admissible, _, _ = tables(b, k)
                indices = max((a for a, good in enumerate(admissible) if good), key=card.__getitem__)
                L = prime//(8*b)
                bins = {4*L*i+e: i for i in range(b) if indices >> i & 1 for e in range(L)}
                initial = flags = 0
                for u in range(prime):
                    for v in range(prime):
                        occupied = {x: bins[y] for x in host
                                    for y in [(u*x+v) % prime] if y in bins}
                        bad = [(x,y) for x,y in cover if x in occupied and y in occupied
                               and occupied[x] == occupied[y]]
                        after = set(occupied) - {x for x,y in bad}
                        assert all(not set(edge) <= after for edge in edges)
                        initial += len(occupied)
                        flags += len(bad)
                        count += 1
                assert initial == len(host)*card[indices]*L*prime
                assert flags == len(cover)*card[indices]*L*L
    return count


def check_composition():
    n = 7
    checked = 0
    for k in (3, 4):
        card, _, _, alpha = tables(n, k)
        def distortion(p):
            worst = Fraction(0)
            for host in range(1, 1 << n):
                m = card[host]
                avg = sum((p**card[a])*(1-p)**(m-card[a])*alpha[a]
                          for a in range(host+1) if a & host == a)
                worst = max(worst, avg / (p*alpha[host]))
            return worst
        half = distortion(Fraction(1, 2))
        third = distortion(Fraction(1, 3))
        sixth = distortion(Fraction(1, 6))
        assert max(half, third) <= sixth <= half*third
        checked += 3*((1 << n)-1)
    return checked


if __name__ == '__main__':
    cases = [(n, k, p) for n in range(1, 11) for k in (3, 4, 5)
             for p in (Fraction(1, 4), Fraction(1, 2), Fraction(2, 3), Fraction(1))]
    cases += [(16, 3, Fraction(1, 4)), (16, 4, Fraction(2, 5)), (16, 5, Fraction(1, 2))]
    print('Ambient random subsets across exact models:', sum(check_model(*case) for case in cases))
    print('Weighted fingerprint tests:', check_fingerprints())
    print('Integer host affine maps:', check_affine_host())
    print('Host-thinning ratios:', check_composition())
