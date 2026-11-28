"""Exact certificates for the sub-golden-ratio Roth growth estimate.

Requires only Python 3.8+; do not disable assertions.
"""
from collections import Counter
from fractions import Fraction


def fibonacci(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def sphere_count():
    dimension, alphabet, target = 12, 38, 702
    charge = Counter(((2*i - 37)**2 - 1)//8 for i in range(alphabet))
    layer = [0] * (target+1)
    layer[0] = 1
    for _ in range(dimension):
        layer = [sum(mult*layer[i-j] for j, mult in charge.items() if j <= i)
                 for i in range(target+1)]
    # Independent coefficient extraction by Kronecker substitution. Even the
    # sum of all coefficients fits in one radix digit.
    radix = 1 << (alphabet**dimension).bit_length()
    mask = radix-1
    polynomial = sum(mult*radix**j for j, mult in charge.items())
    independent = (polynomial**dimension // radix**target) & mask
    assert independent == layer[target] == 19_268_048_304_586_752
    return layer[target]


def verify():
    s = 54
    seed = sphere_count()
    K = fibonacci(114)
    a, b = 2*K-1, 3*K
    start = a
    multiplier = 0
    q = (fibonacci(111)-1)//4
    assert (75**12+1)//2 <= q
    path_edges = 0
    for _ in range(s):
        A, B = a+b, a+2*b+1
        lower, upper = 2*A-B, B-A
        assert a == lower+1 and b == upper-1 and b <= A
        steps, x = 0, a
        while x < b:
            y = min(b, 2*x-lower, (upper+x)//2)
            assert x < y <= b and y+(A-x)+max(y, A-x) <= B
            x = y
            steps += 1
        path_edges += steps
        multiplier = (2*multiplier+1)*steps
        a, b = A, B
    assert a == K*fibonacci(111)-1 and b == K*fibonacci(112)
    ratio = Fraction(b, a)
    assert ratio == Fraction(fibonacci(114), fibonacci(113))
    assert ratio*ratio-ratio-1 < 0
    assert ratio < Fraction(fibonacci(172), fibonacci(171))
    assert (2*q-1)*(start+1) <= a
    gain = Fraction(seed-2**s, seed*multiplier)
    assert gain > Fraction(2, 10**145)
    assert 3*10**290 >= a
    print("Fibonacci dilation:", ratio)
    print("Sphere cardinality:", seed)
    print("Checked interval comparisons:", path_edges)
    print("Error multiplier:", multiplier)
    print("Interpolated gain exceeds 2/10^145.")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Assertions must be enabled.")
    verify()
