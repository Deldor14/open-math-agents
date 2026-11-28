"""Verify all local tests using quartic arithmetic and two split quadratic norms."""
from math import isqrt
from pathlib import Path

ONE = (1, 0, 0, 0)
EPSILON = (0, 0, -1, -1)  # 1 + z + z^{-1} = -z^2-z^3


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def multiply(left, right, m):
    coeff = [0] * 7
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            coeff[i + j] += a * b
    for i in range(6, 3, -1):
        for j in range(i - 4, i):
            coeff[j] -= coeff[i]
    return tuple(v % m for v in coeff[:4])


def power(base, exponent, m):
    value = ONE
    while exponent:
        if exponent % 2:
            value = multiply(value, base, m)
        base = multiply(base, base, m)
        exponent //= 2
    return value


def check_at_exponent(p):
    assert prime(p) and p >= 7 and p % 5 in (2, 3, 4)
    m = p * p
    f = next(f for f in range(1, 5) if pow(p, f, 5) == 1)
    e = p**f - 1
    generator = power(EPSILON, e, m)
    logs = {power(generator, j, m): j for j in range(p)}
    assert len(logs) == p and power(generator, p, m) == ONE

    matches = []
    for x in range(p):
        base = (1-x, x, 0, 0)
        value = power(base, e, m)
        derivative = multiply(power(base, e-1, m), (-1, 1, 0, 0), m)
        for k in range(p):
            lifted = tuple((v + k*p*e*d) % m for v, d in zip(value, derivative))
            if lifted in logs:
                matches.append((logs[lifted], x+k*p))
    assert sorted(matches) == [(0, 0), (0, 1)], (p, matches)


def check_auxiliary(p, q):
    assert prime(q) and q % 5 == 4 and q % p == 1
    k = (q-1)//p
    s = next(s for s in range(q) if s*s % q == 5)
    roots = [(sign*s-1)*pow(2, -1, q) % q for sign in (1, -1)]
    assert len(set(roots)) == 2
    for j, expected in [(0, [0, 1]), (p//2, [])]:
        targets = [pow(1+u, 2*k*j, q) for u in roots]
        matches = []
        for x in range(q):
            y = x*(1-x) % q
            if all(pow((1+(u-2)*y) % q, k, q) == target
                   for u, target in zip(roots, targets)):
                matches.append(x)
        assert matches == expected, (p, q, j, matches)


def main():
    path = Path(__file__).with_name("cyclotomic_witnesses.txt")
    rows = [list(map(int, line.split())) for line in path.read_text().splitlines()]
    assert [r[0] for r in rows] == [p for p in range(29, 240) if prime(p) and p%5 != 1]
    for p, *aux in rows:
        assert aux and len(aux) == len(set(aux))
        check_at_exponent(p)
        for q in aux:
            check_auxiliary(p, q)
    print(f"Verified {len(rows)} exponent-prime tables and {sum(len(r)-1 for r in rows)} auxiliary-prime tables.")


if __name__ == "__main__":
    main()
