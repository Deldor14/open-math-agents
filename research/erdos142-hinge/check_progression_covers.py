"""Check the integer-multiplicity covers and periodic lower certificates in ProgressionCovers.md."""
from collections import Counter
from fractions import Fraction
from math import gcd


def gap_cover(n, N, g):
    q, r = divmod(N, n)
    # The fallback uses the q blocks at the left and a final block at the right.
    if r == 0 or r >= g:
        blocks = Counter({(1 + j * n, 1): 1 for j in range(q)})
        if r:
            blocks[N - n + 1, 1] += 1
        return blocks, 1
    assert g <= q + 1 and r + (n - 1) * g <= N and n % g == 0
    blocks = Counter()
    for j in range(g):
        for b in range(q):
            start = 1 + b * n + (r if b >= j else 0)
            blocks[start, 1] += 1
    for i in range(1, r + 1):
        blocks[i, g] += 1
    return blocks, g


def verify_upper(n, N, g, require_flat=False):
    blocks, multiplicity = gap_cover(n, N, g)
    counts = [0] * N
    for (a, d), m in blocks.items():
        for x in range(a, a + n * d, d):
            assert 1 <= x <= N
            counts[x - 1] += m
    assert min(counts) >= multiplicity
    if require_flat:
        assert max(counts) == multiplicity
    return Fraction(sum(blocks.values()), multiplicity)


def prime_power_base(n):
    p = next(j for j in range(2, n + 1) if n % j == 0)
    m = n
    while m % p == 0:
        m //= p
    return p if m == 1 else None


def verify():
    flat_cases = power_cases = 0
    for n in range(2, 20):
        for N in range(max(n, n * (n - 1)), n * (n - 1) + 3 * n):
            assert verify_upper(n, N, n, True) == Fraction(N, n)
            flat_cases += 1
        p = prime_power_base(n)
        if p is None:
            continue
        for N in range(n, n * (n - 1) + n):
            max_step = (N - 1) // (n - 1)
            g = 1
            while g * p <= min(n, max_step):
                g *= p
            lower = sum((x % n) < g for x in range(N))
            # Every permitted progression has weight one for the periodic test.
            for d in range(1, max_step + 1):
                assert g % gcd(n, d) == 0
                for a in range(min(n, N - (n - 1) * d)):
                    assert sum((a + i * d) % n < g for i in range(n)) == g
            assert verify_upper(n, N, g) == Fraction(lower, g)
            power_cases += 1
    print(f"{flat_cases} uniform covers and {power_cases} matching upper/lower power cases checked")


if __name__ == "__main__":
    verify()
