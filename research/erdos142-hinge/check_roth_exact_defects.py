"""Finite checks for the exact absolute defect manuscript. Python 3, no dependencies."""
from fractions import Fraction
from itertools import combinations, product


def is_free(points):
    points = set(points)
    return all(2 * b - a not in points for a, b in combinations(sorted(points), 2))


def free_families(n):
    family = [()]
    for b in range(n):
        family += [old + (b,) for old in family if is_free(old + (b,))]
    return family


def coversize(A, d):
    edges = [set(triple) for triple in combinations(A, 3)
             if any(abs(sum(triple) - 3 * y) == d for y in triple)]
    for k in range(len(A) + 1):
        if any(all(set(C) & edge for edge in edges) for C in combinations(A, k)):
            return k
    raise AssertionError


def bad_starts(A, t):
    return {x for x in A if any(y - x in (t, 2*t) or 2*(y-x) == t for y in A)}


def check_covers():
    family = free_families(17)
    R = [max(len(A) for A in family if not A or A[-1] < n) for n in range(18)]
    individual = averages = 0
    for A in free_families(9):
        n = A[-1]+1 if A else 0
        for t in range(1, 9):
            cost = coversize(A, t) + coversize(A, 2*t) + len(bad_starts(A, t))
            assert 2 * len(A) <= R[n+t] + 2*cost
            individual += 1
        for b, q, length in product(range(1, 5), range(1, 4), range(1, 7)):
            error = sum(len(bad_starts(A, b+q*j)) for j in range(length))
            assert error <= 3*len(A)*R[length]
            averages += 1
    return individual, averages


def check_fibers():
    models = [max(free_families(k), key=len) for k in range(6)]
    phases = averages = 0
    for A in free_families(7):
        n = A[-1]+1 if A else 1
        for t in range(1, 5):
            if any(abs(x+z-2*y) == t for x,y,z in product(A, repeat=3)):
                continue
            for slope in map(Fraction, ('2/3','1','4/3','3/2','5/3','2','7/3','7/2','4')):
                p, q = slope.numerator, slope.denominator
                # A full phase period of rational half-open tubes, in units of 1/q.
                total = 0
                for h in range(q*t):
                    selected = set()
                    for x in A:
                        low = (p*x+h + q-1)//q
                        top = (p*(x+t)+h + q-1)//q
                        fiber = [y for y in range(low, top) if (y-x) % t == 0]
                        chosen = {fiber[i] for i in models[len(fiber)]}
                        assert not selected.intersection(chosen)
                        selected.update(chosen)
                    assert is_free(selected)
                    if selected:
                        span = max(selected) - min(selected) + 1
                        assert span <= (p*(n-1+t) + q-1)//q
                    phases += 1
                    total += len(selected)
                k, r = divmod(p, q)
                assert total == len(A)*t*((q-r)*len(models[k]) + r*len(models[k+1]))
                averages += 1
    return phases, averages


def check_doubling_matching():
    # A second method counts optimal vertex covers on the paths from odd roots.
    for H in range(1, 1025):
        used = set()
        level = 1
        while level <= H:
            for t in range(H//(4*level)+1, H//(2*level)+1):
                assert t not in used and 2*t not in used
                used.update((t, 2*t))
            level *= 4
        minimum = sum((H//r).bit_length()//2 for r in range(1, H+1, 2))
        assert len(used) == 2*minimum
    return 1024


if __name__ == '__main__':
    print('Finite two-cover inequalities and shift averages:', *check_covers())
    print('Rational fiber phases and complete phase averages:', *check_fibers())
    print('Dyadic matching / minimum cover comparisons:', check_doubling_matching())
