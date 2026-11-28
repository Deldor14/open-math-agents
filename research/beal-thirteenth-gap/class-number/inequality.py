"""Exact lower bound for the unconditional inequality in BDyDF, Corollary 5.2."""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import sys

T = 2**22
K = 256
SCALE = 10**12


def log_near_one(x):
    """Enclose log(x) for rational 1 <= x <= 2 by the atanh series."""
    assert 1 <= x <= 2
    y = (x - 1) / (x + 1)
    terms = 18
    lower = 2 * sum(y**(2*j + 1) / (2*j + 1) for j in range(terms))
    remainder = 2*y**(2*terms+1) / ((2*terms+1)*(1-y*y))
    return lower, lower + remainder


L2, U2 = log_near_one(Q(2))


def log_interval(x):
    x = Q(x)
    shift = 0
    while x > 2:
        shift += 1
        x /= 2
    lo, hi = log_near_one(x)
    return lo + shift*L2, hi + shift*U2


def archimedean():
    gamma_lower = sum(Q(1,k) for k in range(1,1025)) - log_interval(1025)[1]
    # Archimedes' bounds 223/71 < pi < 22/7.
    pi_low, pi_high = Q(223,71), Q(22,7)
    log_rd_upper = (18*U2 + 21*log_interval(7)[1] + 14*log_interval(13)[1])/21
    cost = (pi_high**2/4 + 2*U2/7)/(22*L2)
    return gamma_lower + log_interval(4*pi_low)[0] + Q(1,7) - log_rd_upper - cost


def read_counts(path):
    counts = Counter()
    for line in Path(path).read_text().splitlines():
        norm, count = map(int,line.split())
        assert 2 <= norm < T and count > 0
        counts[norm] += count
    return counts


def main():
    counts = read_counts(sys.argv[1])
    if len(sys.argv) > 2 and counts != read_counts(sys.argv[2]):
        raise ValueError("independent norm counts disagree")
    # log(2)>693147/10^6 is verified directly by the same rational series.
    assert L2 > Q(693147,10**6)
    prime_sum = 0
    for n,count in counts.items():
        j = (n**K).bit_length()-1  # floor(K*log_2(n))
        v = n
        while v < T:
            h = j if v == n else (v**K).bit_length()-1
            numerator = SCALE*4*count*j*693147*max(0,22*K-h-1)
            denominator = 21*(1+v)*10**6*22*K*K
            prime_sum += numerator // denominator
            v *= n
    arch = archimedean()
    arch_floor = (arch.numerator*SCALE)//arch.denominator
    margin = prime_sum + arch_floor
    print("number of ideals:",sum(counts.values()))
    print("distinct norms:",len(counts))
    print("lower bounds with denominator",SCALE)
    print("prime contribution:",prime_sum)
    print("archimedean contribution:",arch_floor)
    print("normalized margin:",margin)
    if margin <= 0:
        raise ArithmeticError("strict inequality was not certified")


if __name__ == "__main__":
    main()
