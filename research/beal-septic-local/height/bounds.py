"""Check the 27-row certificate and derive conservative bounds with q=p omitted."""
from math import isqrt, prod
from pathlib import Path
from sys import argv


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def sixth_root(n):
    low, high = 0, 1
    while high**6 <= n:
        high *= 2
    while high - low > 1:
        mid = (low + high) // 2
        if mid**6 <= n:
            low = mid
        else:
            high = mid
    return low


qs = [q for q in range(13, 998, 7) if prime(q)]
rows = [list(map(int, row.split())) for row in Path(argv[1]).read_text().splitlines()]
assert rows == [[q, 0] for q in qs]


def gap(p, include_diagonal=False):
    return 70 * prod(q for q in qs if (include_diagonal or p != q) and (q-1)%p)


exponents = [p for p in range(11, 1000) if prime(p)] + [1009]
print('auxiliary primes', len(qs), 'non-axis projective classes', sum(q-1 for q in qs))
print('product', prod(qs))
for include in [False, True]:
    branches = [(p, gap(p, include)) for p in exponents]
    p_gap, min_gap = min(branches, key=lambda branch: branch[1])
    p_height, min_pm = min(
        ((p, p*m) for p, m in branches), key=lambda item: item[1])
    print('include q=p', include)
    print('d at least', min_gap, 'minimum at', p_gap)
    print('5*u^6 strictly above', min_pm, 'minimum at', p_height)
    print('u at least', sixth_root(min_pm//5)+1)
    odd_bound = (sixth_root(min_pm//5)//2)*2+1
    if odd_bound**6*5 <= min_pm:
        odd_bound += 2
    print('odd u at least', odd_bound)
    print('ab at least', prod(qs) if include else prod(qs)//max(qs))
    if include:
        print('fixed divisor of d',70*prod(q for q in qs if all((q-1)%p for p in exponents)))
