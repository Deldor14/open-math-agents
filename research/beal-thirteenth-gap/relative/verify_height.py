"""Global relative-gap certificate for thirteenth powers. Python standard library."""
from decimal import Decimal, localcontext
from fractions import Fraction
from math import isqrt

K = 16000


def verify(p):
    # A geometric upper bound for u when h^K <= u^p.
    exponent = (K + (K-p) - 1)//(K-p)
    U = (2*p)**exponent
    Q = U**12
    bits = 2*Q.bit_length() + 32
    S = 1 << bits
    assert Q*Q*1000 < S
    # 4095/p < 1, u >= 2 and 2p/K < 2 imply r-alpha < 2^(2-2p).
    assert bits + 2 < 2*p
    with localcontext() as ctx:
        ctx.prec = bits*30103//100000 + 40
        guess = int(Decimal(S)*(-Decimal(4096).ln()/p).exp())

    def power_bound(x, round_up):
        guard = 1 << 64
        unit = S*guard
        adjustment = unit-1 if round_up else 0
        def mul(a,b):
            return (a*b+adjustment)//unit
        answer, base, n = unit, x*guard, p
        while n:
            if n % 2:
                answer = mul(answer,base)
            base = mul(base,base)
            n //= 2
        return 4096*answer-unit

    # The exact enclosing comparisons ignore the accuracy of Decimal.
    assert power_bound(guess-1,True) < 0 < power_bound(guess+2,False)
    lower,upper = guess-1,guess+3
    # The closest rational to the midpoint with denominator <= Q must
    # lie in this closed interval if any admissible fraction does.
    mid = Fraction(lower+upper,2*S)
    nearest = mid.limit_denominator(Q)
    assert S*nearest.numerator < lower*nearest.denominator or (
        S*nearest.numerator > upper*nearest.denominator), p
    # Exhibit a Farey gap. Its determinant and denominator-sum conditions
    # independently prove the exclusion, regardless of the search routine.
    a,b = nearest.numerator, nearest.denominator
    assert b > 1
    sign = 1 if S*a < lower*b else -1
    residue = (-sign*pow(a,-1,b)) % b
    neighbor_den = Q - (Q-residue) % b
    neighbor_num = (a*neighbor_den+sign)//b
    c,d = neighbor_num,neighbor_den
    if sign < 0:
        a,b,c,d = c,d,a,b
    assert b > 0 and d > 0 and b*c-a*d == 1 and b+d > Q
    assert a*S < lower*b and upper*d < c*S
    return bits


def main():
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    assert 1000**5 > 12000**3
    count = maximum = 0
    for p in range(6001,15400,2):
        if all(p % d for d in range(3,isqrt(p)+1,2)):
            maximum = max(maximum, verify(p))
            count += 1
    print('Prime exponents examined:', count)
    print('Largest dyadic precision:', maximum, 'bits')
    print('Rational intervals with any admissible denominator: 0')


if __name__ == '__main__':
    main()
