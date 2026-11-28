"""Verify coverage, both relative class-number tests and the independent PARI sample."""
from math import isqrt
from pathlib import Path

root = Path(__file__).resolve().parent


def rows(name):
    return [tuple(map(int, line.split())) for line in (root / name).read_text().splitlines()]


def primes(bound):
    return [p for p in range(11, bound + 1)
            if p % 7 in (2, 3, 4, 5) and all(p % d for d in range(2, isqrt(p) + 1))]


direct = rows('character-values.txt')
polynomial = rows('bernoulli.txt')
assert direct == polynomial
assert [p for p, _, _ in direct] == primes(20000)
passing = {p for p, a, b in direct if a == b == 0}
assert rows('exponents.txt') == [(p,) for p in sorted(passing)]
sample = rows('class-sample.txt')
assert [p for p, _, _ in sample] == primes(5000)
for p, plus_bound, minus in sample:
    assert (p in passing) == (plus_bound == minus == 0)
assert len(passing) == 606 and len(direct) == 1503
print(len(direct), 'inert primes,', len(passing), 'excluded signatures,',
      len(sample), 'independent full-class-group tests')
