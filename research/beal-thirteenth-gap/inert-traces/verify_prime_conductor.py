"""Verify the eight exact quadratic identities and an independent field trace."""
from fractions import Fraction
from math import isqrt

from real_trace import real_traces


def fourier_scaled_trace(l, j):
    def four_c(k):
        a, b, d = [(-(k + r) * pow(2, -1, l)) % l for r in (1, 2, 3)]
        return (2 * (-1)**a
                + 3 * (-1)**b * (2*b + 2 - l)
                + (-1)**d * (2*(d+1)*(d+2) - l*(2*d+3)))

    return four_c(0) + four_c(2*j) - 2*four_c(j)


def table(l, j):
    if l % 4 == 1:
        entries = (-j*j, 3*j*j-2*l*j-5, 2*l*l-3*j*j+12*l-12*j+10,
                   j*j+2*l*j+12*j+5)
    else:
        entries = (j*j, -j*j-2*l*j+12*j-5, -2*l*l+3*j*j+12*l-12*j-10,
                   -3*j*j+2*l*j+5)
    return entries[j % 4]


def certify_cell(e, h):
    # Translate a triangular stencil. A quadratic vanishing on this stencil
    # is zero: three points on the first line, two on the next, one on the last.
    for u, v in ((0, 0), (1, 0), (2, 0), (0, 1), (1, 1), (0, 2)):
        l = 40 + e + 4*u
        j = 4 + h + 4*v
        assert 0 < 2*j < l
        # Fourier computation and the substitution in the proof apply to
        # composite odd l, too, as they sum over all l-th roots.
        assert table(l, j) == fourier_scaled_trace(l, j)


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))


def exceptional_primes(l):
    row = [table(l, j)//4 for j in range(1, (l+1)//2)]
    return [p for p in range(3, max(map(abs, row))+1, 2)
            if prime(p) and p != l and row[min(p % l, l-p % l)-1] % p == 0]


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Assertions must be enabled.")
    for e in (1, 3):
        for h in range(4):
            certify_cell(e, h)
    count = 0
    for l in filter(prime, range(5, 74)):
        for j, actual in enumerate(real_traces(l), 1):
            scaled = table(l, j)
            assert scaled % 4 == 0 and 0 < abs(scaled) <= 2*(l+1)*(l+5)
            assert scaled == fourier_scaled_trace(l, j)
            assert actual == l*Fraction(scaled, 4)
            count += 1
    assert [exceptional_primes(l) for l in (5, 7, 11, 13)] == [[3, 7], [], [5], [5]]
    print(f"All eight polynomial identities and {count} independent field traces agree.")
