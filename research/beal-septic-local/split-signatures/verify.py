"""Check all split-prime rows and the character cancellation in the lifting lemma."""
from math import isqrt
from pathlib import Path

root = Path(__file__).resolve().parent


def rows(filename):
    return [tuple(map(int, line.split())) for line in (root / filename).read_text().splitlines()]


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


expected = [p for p in range(11, 20001) if p % 7 in (1, 6) and prime(p)]
first = rows('bernoulli.txt')
assert first == rows('character-values.txt')
assert [p for p, _, _ in first] == expected
passing = [p for p, a, b in first if a == b == 0]
assert rows('exponents.txt') == [(p,) for p in passing]
assert len(passing) == 328 and len(first) == 755
for p in (13, 29, 41, 43):
    powers = list(range(1, p))
    for i in range(1, p - 1):
        assert sum(powers) % p == 0
        powers = [x * a % p for a, x in enumerate(powers, 1)]
    assert sum(powers) % p == p - 1
print(len(first), 'split primes;', len(passing), 'cube-divisibility certificates')
