"""Extract primitive positive square-plus-cube solutions from published curve invariants."""
import hashlib
import json
import math
import re
import sys
from pathlib import Path


def root(value, exponent):
    """Floor of the positive integer root, using integer arithmetic only."""
    lo, hi = 0, 1 << ((value.bit_length() + exponent - 1) // exponent)
    while lo < hi:
        middle = (lo + hi + 1) // 2
        if middle ** exponent <= value:
            lo = middle
        else:
            hi = middle - 1
    return lo


def exponents(value):
    if value == 1:
        return ['all']
    return [n for n in range(2, value.bit_length()) if root(value, n)**n == value]


def extract(path, bound):
    solutions, counts = set(), {}
    primes = {n for n in range(3, bound + 1, 2)
              if all(n % p for p in range(2, math.isqrt(n) + 1))}
    section = None
    for line in path.read_text().splitlines():
        if line.startswith('# S = '):
            places = list(map(int, re.findall(r'\d+', line)))
            section = None
            if places == [2, 3]:
                section = 3
            if len(places) == 3 and places[:2] == [2, 3] and places[2] in primes:
                section = places[2]
            if section:
                counts[section] = 0
        elif section and line.startswith('('):
            counts[section] += 1
            c4,c6 = map(int, line.strip('()').split(','))
            if c4 >= 0 or c6 == 0:
                continue
            num, den = -c4**3, c6**2
            common = math.gcd(num,den)
            cube,square = num//common,den//common
            v,u = root(cube,3),math.isqrt(square)
            if v**3 != cube or u*u != square:
                continue
            total = cube + square
            k = 0
            while total % section == 0:
                k += 1
                total //= section
            if total == 1 and k >= 3:
                assert math.gcd(v,u) == 1
                solutions.add((section,k,u,v))
    assert set(counts) == primes, sorted(primes - set(counts))
    return {'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'curve_rows':sum(counts.values()), 'sections':counts,
            'solutions':sorted(solutions),
            'square_root_is_a_power':[(*r,exponents(r[2])) for r in sorted(solutions) if exponents(r[2])]}


if __name__ == '__main__':
    print(json.dumps(extract(Path(sys.argv[1]),int(sys.argv[2])),indent=2))
