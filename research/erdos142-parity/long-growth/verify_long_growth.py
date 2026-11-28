"""Exact arithmetic for the four-term example in LongGrowth.md."""
from collections import Counter
from fractions import Fraction
from math import prod


def orbit(q, steps):
    u, v = q, q + 1
    for _ in range(steps):
        u, v = u + (q - 1) * v, u + q * v
    return u, v


def certify(q, steps, seed, modulus):
    u, v = orbit(q, steps)
    unext, K = orbit(q, steps + 1)
    assert u * K - v * unext == 1
    a, b = K * q - 1, K * (q + 1)
    start = a
    error, comparisons = 0, 0
    for _ in range(steps):
        A, B = a + (q - 1) * b, a + q * b + 1
        upper = B - A
        lower = A - (q - 1) * upper
        x, count = a, 0
        while x < b:
            y = min(b, x + (x - lower) // (q - 1), (upper + x) // 2)
            gap = upper - (y - x)
            assert x < y <= b <= A
            assert y <= gap and A - x <= (q - 1) * gap
            assert y + gap + A - x == B
            count += 1
            x = y
        error = (q * error + q - 1) * count
        comparisons += count
        a, b = A, B
    assert a == K * u - 1 and b == K * v
    assert modulus * start <= a and seed > q**steps
    ratio = Fraction(b, a)
    assert ratio == Fraction(K, unext)
    assert (q - 1) * ratio * (ratio - 1) < 1
    gain = Fraction(seed - q**steps, seed * error)
    return a, ratio, gain, comparisons


def four_term():
    q, steps, d, h = 3, 184, 2048, 29
    ranges = 1 + h * (d - 1)**2
    seed = (d**h + ranges - 1) // ranges
    modulus = (2 * d - 1)**h
    u, _ = orbit(q, steps)
    assert modulus <= u // (2 * q)
    a, ratio, gain, count = certify(q, steps, seed, modulus)
    power = len(str((2 * gain.denominator + gain.numerator - 1) // gain.numerator))
    assert gain >= Fraction(2, 10**power)
    # r_k(n) >= sqrt(n/3); losses from taking an integer grid cost at most a.
    threshold_power = 2 * (len(str(2 * a)) + power) + 1
    assert 10**threshold_power >= 3 * (2 * a * 10**power)**2
    print('Four-term example, exact dilation', ratio)
    print('Allowed gain 10^(-%s), for n >= 10^%s' % (power, threshold_power))
    print('Interval comparisons', count)
    return power, threshold_power


def mixed_three_term():
    alphabets = [24] * 2 + [26] * 11
    energy = 348
    ways = [1] + [0] * energy
    radix = 1 << prod(alphabets).bit_length()
    packed = 1
    for d in alphabets:
        charge = Counter(((2*j - d + 1)**2 - 1)//8 for j in range(d))
        ways = [sum(m * ways[e-i] for i, m in charge.items() if i <= e)
                for e in range(energy+1)]
        packed *= sum(m * radix**i for i, m in charge.items())
    seed = ways[energy]
    assert seed == (packed // radix**energy) % radix == 9_436_763_481_513_984
    modulus = prod(2*d - 1 for d in alphabets)
    a, ratio, gain, steps = certify(2, 53, seed, modulus)
    assert ratio < Fraction(orbit(2,55)[1], orbit(2,55)[0])
    power = len(str((2 * gain.denominator + gain.numerator - 1) // gain.numerator))
    assert gain >= Fraction(2, 10**power)
    # Use the rational-grid Roth interpolant in EffectiveGrowth.md:
    # rounding up only the seed domain costs at most one site there.
    K = orbit(2, 54)[1]
    assert modulus * (2*K) <= a
    assert 3 * 10**(2*power) >= a
    print('Three-term mixed-radix example, dilation', ratio)
    print('Allowed gain 10^(-%s), for n >= 3 * 10^%s' % (power, 2*power))
    print('Interval comparisons', steps)
    return power


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    four_term()
    mixed_three_term()
