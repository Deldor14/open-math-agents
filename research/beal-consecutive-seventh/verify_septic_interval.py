"""Independent integer enclosure and least-denominator check.

Decimal supplies guesses. Multiplication with outward integer rounding certifies
each root interval. No transcendental library output is needed for correctness.
"""
from decimal import Decimal, localcontext
from math import isqrt

BOUND = 275184
S = 1 << 352


def primes():
    composite = set()
    for j in range(2,isqrt(BOUND)+1):
        if j not in composite:
            composite.update(range(j*j,BOUND+1,j))
    return (p for p in range(11,BOUND+1) if p not in composite)


def power_interval(n,p):
    low = high = S
    a = b = n
    while p:
        if p & 1:
            low = low*a//S
            high = (high*b+S-1)//S
        a,b = a*a//S,(b*b+S-1)//S
        p //= 2
    return low,high


def simplest(A,B,C,D):
    """Numerator/denominator componentwise-minimal in [A/B,C/D]."""
    prefix=[]
    while True:
        low=(A+B-1)//B
        if low*D<=C:
            a,b=low,1
            break
        k=A//B
        prefix.append(k)
        A,B,C,D=D,C-k*D,B,A-k*B
    for k in reversed(prefix):
        a,b=k*a+b,a
    return a,b


def small(u,p):
    d=u**p
    # Directly test the original sum; (d-1)/2 and (d+1)/2 are consecutive.
    a=(d-1)//2
    n=a**7+(a+1)**7
    lo,hi=0,1<<((n.bit_length()+p-1)//p)
    while hi-lo>1:
        mid=(hi+lo)//2
        if mid**p>n:hi=mid
        else:lo=mid
    if lo**p==n or hi**p==n:
        raise AssertionError((p,u))


def check():
    tested=large=near=0
    for u in range(3,4000,2):
        small(u,5)
        tested+=1
    with localcontext() as ctx:
        ctx.prec=125
        log_inv64=-Decimal(64).ln()
        for p in primes():
            if p<120:
                for u in range(3,12*p,2):
                    small(u,p)
                    tested+=1
                continue
            large+=1
            guess=int((log_inv64/p).exp()*S)
            left,right=guess-4096,guess+4096
            assert 64*power_interval(left,p)[1]<S
            assert 64*power_interval(right,p)[0]>S
            # 63/(p*3^(2p)) < 1/S already for p>=120.
            assert 120*3**240>63*S
            right+=1
            limit=(12*p)**6
            assert (right-left)*limit**2<S
            n,d=simplest(left,S,right,S)
            assert left*d<=S*n<=right*d
            if d<=limit:
                near+=1
                # Distinct reduced fractions with denominator <=limit are
                # separated by >=1/limit^2. Check this unique possibility.
                if d>=729 and d%2 and isqrt(d)**2==d:
                    low,high=1,12*p
                    while high-low>1:
                        m=(low+high)//2
                        if m**6<=d:low=m
                        else:high=m
                    if low**6==d:
                        # Modular certificate for an impossible exact root.
                        a=pow(low,p,127)
                        f=(a**6+21*a**4+35*a*a+7)%127
                        if f==64*pow(n,p,127)%127:
                            raise AssertionError((p,low,n))
    print('Direct checks of original sums:',tested)
    print('Certified root intervals for p>=120:',large)
    print('Intervals containing any rational with admissible denominator bound:',near)
    print('Remaining candidates: 0')


if __name__=='__main__':
    check()
