"""Farey certificates for D < |a-b|^13000 in the eleventh-power subcase."""
from decimal import Decimal, localcontext
from math import isqrt
from fractions import Fraction

EXP = 13000


def prime(p):
    return all(p % i for i in range(2,isqrt(p)+1))


def neighbours(n,d,limit):
    a,b,c,e = 0,1,1,0
    while d:
        k,r = divmod(n,d)
        if b+k*e > limit:
            k = (limit-b)//e
            a,b = a+k*c,b+k*e
            return (a,b,c,e) if a*e < b*c else (c,e,a,b)
        a,b,c,e = c,e,a+k*c,b+k*e
        n,d = d,r
    raise AssertionError("Centre has small denominator.")


def power_outward(x,p,S,up):
    # The addition of S-1 changes a floor to a ceiling for nonnegative integers.
    offset = S-1 if up else 0
    prod = S
    while p:
        if p%2:
            prod = (prod*x+offset)//S
        x = (x*x+offset)//S
        p //= 2
    return prod


def exp_lower(x):
    term = Fraction(1)
    total = term
    for k in range(1,51):
        term = term*x/k
        total += term
    return total


def run():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    assert exp_lower(Fraction(962,100)) > 13001
    assert exp_lower(Fraction(1032,100)) > 30001
    assert 126*Fraction(107,10)**2 < 15000
    exponents = [p for p in range(5001,12602) if prime(p)]
    maxbits = count = 0
    # High-precision Decimal only proposes a centre. All acceptance tests are integral.
    with localcontext() as ctx:
        ctx.prec = 3300
        log_inv = -Decimal(1024).ln()
        for p in exponents:
            remaining = EXP-p
            degree = (EXP+remaining-1)//remaining
            bound = (2*p)**(10*degree)
            bits = 2*bound.bit_length()+48
            maxbits = max(maxbits,bits)
            scale = 1 << bits
            assert 1023*scale < p*3**p
            with localcontext() as inner:
                inner.prec = bits*31//100+30
                assert inner.prec <= ctx.prec
                z = int((log_inv/p).exp()*scale)
            margin = 1 << 18
            lo, hi = z-margin, z+margin
            assert 1024*power_outward(lo,p,scale,True) < scale
            assert scale < 1024*power_outward(hi,p,scale,False)
            # One additional dyadic unit covers the gap-dependent correction.
            hi += 1
            a,b,c,d = neighbours(z,scale,bound)
            assert b>0 and d>0 and b*c-a*d == 1
            assert b+d > bound
            assert a*scale < lo*b and hi*d < c*scale
            count += 1
    print("Prime exponents, certificates verified:",count)
    print("Largest dyadic precision in bits:",maxbits)
    print("Intervals admitting a reduced fraction with denominator within the bound: 0")


if __name__ == "__main__":
    run()
