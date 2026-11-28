"""Compare two calculations of the local unit map of Q(zeta_7)."""
from itertools import combinations
from math import isqrt
import sys


def multiply(a, b, modulus):
    # Ordinary convolution followed by reduction by Phi_7.
    product = [0] * 11
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            product[i+j] += ai*bj
    for k in range(10, 5, -1):
        for j in range(k-6, k):
            product[j] -= product[k]
    return [c % modulus for c in product[:6]]


def power(a, exponent, modulus):
    result = [1, 0, 0, 0, 0, 0]
    while exponent:
        if exponent % 2:
            result = multiply(result, a, modulus)
        exponent //= 2
        if exponent:
            a = multiply(a, a, modulus)
    return result


def fermat_columns(p):
    f = next(f for f in range(1, 7) if pow(p, f, 7) == 1)
    cols = []
    for i in [1, 2]:
        unit = [1, 0, 0, 0, 0, 0]
        unit[i] = 1
        value = power(unit, p**f-1, p*p)
        value[0] -= 1
        assert all(c % p == 0 for c in value)
        cols.append([c//p for c in value])
    return cols


def frobenius_columns(p):
    # (U^p/sigma(U)-1)/p via binomial coefficients. Work cyclically.
    inverse = [0, 1]
    for j in range(2, p):
        inverse.append(p - (p//j)*inverse[p%j] % p)
    cols = []
    for i in [1, 2]:
        numer = [0]*7
        for j in range(1, p):
            numer[(i*j)%7] += inverse[j] if j%2 else -inverse[j]
        # Since Z^7=1, 2/(1+Z^s) = sum_{k=0}^6 (-Z^s)^k.
        cyc = [sum((-1)**k*numer[(z-i*p*k)%7] for k in range(7))
               * ((p+1)//2) % p for z in range(7)]
        cols.append([(c-cyc[6])%p for c in cyc[:6]])
    return cols


def pivot(columns, p):
    a, b = columns
    for j, k in combinations(range(6), 2):
        determinant = (a[j]*b[k]-a[k]*b[j]) % p
        if determinant:
            return j, k, determinant
    return -1, -1, 0


def main():
    for p in range(11, int(sys.argv[1])+1, 2):
        if not all(p%d for d in range(3, isqrt(p)+1, 2)):
            continue
        left = fermat_columns(p)
        right = frobenius_columns(p)
        # U^{p^f-1} is the product of the f iterated conjugate
        # Frobenius quotients to powers p^i. Only the i=0 term survives.
        # So the first log is sigma^{f-1} of the second.
        invp = pow(p, -1, 7)
        for a, b in zip(left, right):
            cyc = [0]*7
            for k, value in enumerate(b):
                cyc[(k*invp)%7] = value
            assert a == [(c-cyc[6])%p for c in cyc[:6]]
        print(p, *pivot(left, p), *pivot(right, p))


if __name__ == '__main__':
    main()
