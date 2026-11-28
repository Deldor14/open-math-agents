"""Exact regression checks for the effective length and its residue witness."""
from fractions import Fraction
from functools import lru_cache
from math import comb

from check_roth_critical_sampling import tables


@lru_cache(maxsize=None)
def extrema(n, k):
    card, good, _, alpha = tables(n, k)
    return card, good, alpha


def progression_masks(n, k):
    return [sum(1 << (a+i*d) for i in range(k))
            for d in range(1, (n-1)//(k-1)+1)
            for a in range(n-(k-1)*d)]


def ceil_ratio(x):
    return (x.numerator+x.denominator-1)//x.denominator


def residue_witness(n, k, b):
    card_b, good, _ = extrema(b, k)
    seed = max((x for x in range(1 << b) if good[x]), key=card_b.__getitem__)
    residues = [i for i in range(b) if seed >> i & 1]
    card = extrema(n, k)[0]
    best = []
    largest = -1
    for shift in range(2*b):
        classes = [sum(1 << x for x in range((shift+i) % (2*b), n, 2*b))
                   for i in residues]
        occupied = sum(card[c] for c in classes)
        if occupied > largest:
            largest = occupied
            best = classes
    mask = sum(best)
    assert card[mask]*(2*b) >= n*len(residues)
    for edge in progression_masks(n, k):
        if edge & mask == edge:
            assert any(edge & c == edge for c in best)
    return best, mask


def compare(n, k, probabilities):
    card, _, alpha = extrema(n, k)
    masks = range(1 << n)
    layer_sum = [0]*(n+1)
    for a in masks:
        layer_sum[card[a]] += alpha[a]
    witnesses = {}
    catalogs = {}
    total = 0
    for p in probabilities:
        b = ceil_ratio(n*p**(k-1))
        R = extrema(b, k)[-1][-1]
        T = p*n*R/b
        if b not in witnesses:
            classes, mask = residue_witness(n, k, b)
            measured = [0]*(n+1)
            for a in masks:
                value = sum(alpha[a & c] for c in classes)
                assert value == alpha[a & mask] <= alpha[a]
                measured[card[a]] += value
            witnesses[b] = mask
            catalogs[b] = measured
            total += 1 << n
        v = card[witnesses[b]]
        u, w = p.numerator, p.denominator
        masses = [u**r*(w-u)**(n-r) for r in range(n+1)]
        actual = Fraction(sum(a*m for a, m in zip(layer_sum, masses)), w**n)
        restricted = Fraction(sum(a*m for a, m in zip(catalogs[b], masses)), w**n)
        assert actual >= restricted >= p*v/5 >= T/10
        if (n*p).denominator == 1:
            r = int(n*p)
            normalizer = comb(n, r)
            assert Fraction(layer_sum[r],normalizer) >= Fraction(catalogs[b][r],normalizer) >= T/10
    return total


def check_affine():
    cases = 0
    for n, P in ((5,11), (7,17)):
        for k in (3,4):
            edges = progression_masks(n,k)
            for C in range(1 << n):
                card = extrema(n,k)[0]
                cover = {e & (e-1) for e in edges if e & C == e}
                for length in range(1,n+1):
                    R = extrema(length,k)[-1][-1]
                    for u in range(1,P):
                        for v in range(P):
                            line = sum(1 << ((u*i+v) % P) for i in range(length))
                            assert card[C & line] <= R + sum(g & line == g for g in cover)
                            cases += 1
    return cases


if __name__ == '__main__':
    witness_checks = models = 0
    for n in range(1, 14):
        for k in (3,4,5):
            probabilities = {Fraction(i,n) for i in range(1,n+1)}
            probabilities.update((Fraction(1,7), Fraction(1,2), Fraction(3,5)))
            witness_checks += compare(n, k, sorted(probabilities))
            models += len(probabilities)
    print('Bernoulli parameter settings:', models)
    print('Sample and residue masks:', witness_checks)
    print('Affine pointwise restrictions:', check_affine())
