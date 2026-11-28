"""Exact finite checks for planted samples and independent displacements."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
from math import comb


@lru_cache(maxsize=None)
def popcount(mask):
    return bin(mask).count('1')


def progression_edges(n, k):
    return [sum(1 << (a+j*d) for j in range(k))
            for d in range(1, (n-1)//(k-1)+1)
            for a in range(n-(k-1)*d)]


def free_table(n, k):
    edges = progression_edges(n, k)
    return [all(mask & edge != edge for edge in edges) for mask in range(1 << n)]


def sites(mask):
    return [x for x in range(mask.bit_length()) if mask >> x & 1]


def subsets(mask):
    sub = mask
    while True:
        yield sub
        if not sub:
            return
        sub = (sub-1) & mask


def check_samples():
    count = 0
    for k in (3, 4):
        n = 10
        free = free_table(n, k)
        maximal = [a for a, valid in enumerate(free) if valid and
                   all(not free[a | 1 << x] for x in range(n) if not (a >> x & 1))]
        optimum = max(popcount(a) for a in maximal)
        # Two covers. The second has containers containing progressions.
        for extra in (0, 3):
            family = {a | extra for a in maximal}
            cap = max(popcount(c) for c in family)
            ranks = Counter(popcount(a) for a, valid in enumerate(free) if valid)
            for s, size in ranks.items():
                assert comb(optimum, s) <= size <= len(family)*comb(cap, s)
            for a in maximal:
                m = popcount(a)
                for s in range(m+1):
                    samples = [u for u in subsets(a) if popcount(u) == s]
                    for d in range(1, m+1):
                        bad = 0
                        for sample in samples:
                            if any(not (sample & ~c) and popcount(a & ~c) >= d
                                   for c in family):
                                bad += 1
                            else:
                                assert all(popcount(b & ~a) <= cap-m+d-1 for b in maximal
                                           if not (sample & ~b))
                            count += 1
                        assert bad <= len(family)*comb(m-d, s)
    return count


def check_displacements():
    outcomes = 0
    for k in (3, 4):
        n = 6
        allowed = free_table(n, k)
        for t in (1, 2):
            offsets = (0, t, 2*t)
            N = n+2*t
            free = free_table(N, k)
            maximal = [mask for mask, valid in enumerate(free) if valid and
                       all(not free[mask | 1 << x] for x in range(N) if not (mask >> x & 1))]
            alpha = [max(popcount(mask & c) for c in maximal) for mask in range(1 << N)]
            for a, admissible in enumerate(allowed):
                if not admissible:
                    continue
                base = sites(a)
                copies = [a << offset for offset in offsets]
                overlap = sum(popcount(i & j) for i, j in combinations(copies, 2))
                # Weighted expected label occupancy, in units of one sixth.
                for c in maximal:
                    weighted = sum(w*popcount(c & shift) for w, shift in zip((1, 3, 2), copies))
                    assert weighted <= 3*(popcount(c)+overlap)
                for labels in product(range(3), repeat=len(base)):
                    image = 0
                    for x, j in zip(base, labels):
                        image |= 1 << (x+offsets[j])
                    assert len(base)-popcount(image) <= overlap
                    assert alpha[image] >= max(Counter(labels).values(), default=0)
                    outcomes += 1
    return outcomes


def check_affine_sampler():
    cases = 0
    for n, prime in ((5, 11), (6, 13), (8, 17)):
        k = 3
        free = free_table(n, k)
        for ell in range(2, n+1):
            R = max(popcount(m) for m, ok in enumerate(free[:1 << ell]) if ok)
            line_masks = []
            for slope in range(1, prime):
                for start in range(prime):
                    line_masks.append(sum(1 << ((start+slope*i) % prime) for i in range(ell)))
            for C in range(1 << n):
                edges = [e for e in progression_edges(n, k) if e & C == e]
                # Give each AP a two-point subedge and deduplicate all subedges.
                cover = {e & (e-1) for e in edges}
                # Verify the pointwise deletion inequality on every image,
                # then its expectation with denominators cleared.
                assert all(popcount(C & line) <= R + sum(g & line == g for g in cover)
                           for line in line_masks)
                assert (prime-1)*ell*popcount(C) <= prime*(prime-1)*R+len(cover)*ell*(ell-1)
                cases += len(line_masks)
    return cases


if __name__ == '__main__':
    print('Sample and threshold instances:', check_samples())
    print('Displaced labelled images:', check_displacements())
    print('Affine sample and cover instances:', check_affine_sampler())
