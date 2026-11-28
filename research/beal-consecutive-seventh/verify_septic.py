"""Exact check for the last finite step for consecutive seventh powers.

Python 3 standard library. All approximations below have a proved absolute
error in scaled integer units. No floating-point functions are used.
"""
from fractions import Fraction
from math import factorial, isqrt

SCALE = 1 << 352
TERMS = 80
P_MAX = 275184
LOG2_LO = sum((Fraction(2, (2*j+1)*3**(2*j+1)) for j in range(128)), Fraction(0))
LOG2_HI = LOG2_LO + Fraction(3, 3**257)
LOG2_INT = int(SCALE * LOG2_LO)
assert LOG2_INT == int(SCALE * LOG2_HI)
assert factorial(TERMS + 1) > SCALE
assert 200 * 4 * (12 * P_MAX)**12 < SCALE


def approximate(p):
    """Return z such that |z/SCALE - 2^(-6/p)| < 200/SCALE for p>=11."""
    h = 6 * LOG2_INT // p
    assert 2*h < SCALE
    z = term = SCALE
    for i in range(1, TERMS+1):
        term = term*h // (SCALE*i)
        z += -term if i % 2 else term
        if term == 0:
            break   # all later integer terms in the fixed 80-term sum are zero
    return z


def convergents(a,b,bound):
    x_prev, x, y_prev, y = 1, 0, 0, 1
    # Coefficients begin after the initial zero for a/b in (0,1).
    while a:
        quotient, rem = divmod(b, a)
        x_prev,x = x, quotient*x+x_prev
        y_prev,y = y, quotient*y+y_prev
        if y > bound:
            return
        yield x,y
        b,a = a,rem


def integer_root(n,k):
    """Floor of the nonnegative k-th root by integer bisection."""
    lo,hi = 0,1 << ((n.bit_length()+k-1)//k)
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**k<=n:
            lo=mid
        else:
            hi=mid
    return hi if hi**k<=n else lo


def prime_exponents():
    prime = bytearray([1])*(P_MAX+1)
    prime[0:2] = bytes(2)
    for t in range(2,isqrt(P_MAX)+1):
        if prime[t]:
            for i in range(t*t,P_MAX+1,t):
                prime[i]=0
    return [n for n in range(11,P_MAX+1) if prime[n]]


def polynomial(d):
    return d**6+21*d**4+35*d*d+7


def excluded(u,v,p):
    for m in (127,257,509,1009,2017,4093,8191):
        if (64*pow(v,p,m)-polynomial(pow(u,p,m)))%m:
            return True
    return 64*v**p != polynomial(u**p)


def run():
    exponents=prime_exponents()
    nconv=nperfect=0
    for p in exponents:
        for v,y in convergents(approximate(p),SCALE,(12*p)**6):
            nconv+=1
            if y<3**6 or y%2==0:
                continue
            square=isqrt(y)
            if square*square!=y:
                continue
            u=integer_root(square,3)
            if u**3!=square:
                continue
            nperfect+=1
            if not excluded(u,v,p):
                raise AssertionError((p,u,v))
    nsmall=0
    for u in range(3,4000,2):
        numerator=polynomial(u**5)
        assert numerator%64==0
        val=numerator//64
        v=integer_root(val,5)
        if v**5==val:
            raise AssertionError((5,u,v))
        nsmall+=1
    print('Prime exponents >=11:',len(exponents))
    print('Convergents within denominator bound:',nconv)
    print('Odd sixth-power denominators with u>=3:',nperfect)
    print('Quintic-exponent roots checked separately:',nsmall)
    print('Remaining candidates: 0')


if __name__=='__main__':
    run()
