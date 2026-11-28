"""A second integer proof of the bounded-gap sieve, by rational intervals.

It uses neither the convergents nor the fixed-point exponential of the first
verifier. See the text on minimal denominators and on outward powers.
"""
from decimal import Decimal,localcontext
from math import gcd,isqrt
from verify_septic_interval import primes,simplest

S=1<<704
H=10**6

def ends(x,p):
    a=b=x; lo=hi=S
    while p:
        if p%2:
            lo=lo*a//S; hi=(hi*b+S-1)//S
        a,b=a*a//S,(b*b+S-1)//S
        p//=2
    return lo,hi


def sixth(d):
    a=isqrt(d)
    if a*a!=d:return 0
    l,h=0,1<<((a.bit_length()+2)//3)
    while l+1<h:
        m=(l+h)//2
        if m**3<=a:l=m
        else:h=m
    if h**3==a:return h
    return l if l**3==a else 0


def direct(p,u,v):
    s=u**p
    if s<=1:return
    target=(u*v)**p
    # Test odd h=2j+1 via the original sum normalised by no coefficients.
    low,high=0,(min(H,s-1)-1)//2
    while low<=high:
        j=(low+high)//2; h=2*j+1
        a=(s-h)//2
        n=a**7+(a+h)**7
        if n==target:
            assert gcd(a,h)!=1,(p,u,v,h)
            return
        if n<target:low=j+1
        else:high=j-1


def run():
    count=boxes=tests=0
    with localcontext() as ctx:
        ctx.prec=235
        log_inv64=-Decimal(64).ln()
        for p in primes():
            count+=1
            z=int((log_inv64/p).exp()*S)
            l,r=z-4096,z+4096
            assert 64*ends(l,p)[1]<S<64*ends(r,p)[0]
            intervals=[(3,12*p*H-1)]
            while intervals:
                U,V=intervals.pop()
                boxes+=1
                den=p*U**(2*min(p,260))
                right=r+(S*63*H*H+den-1)//den
                if U==V:
                    if U%2==0:continue
                    y=U**6
                    for n in range(max(1,(l*y+S-1)//S),min(y,right*y//S)+1):
                        if gcd(U,n)==1:
                            direct(p,U,n)
                            tests+=1
                    continue
                bound=V**6
                if (right-l)*bound**2 < S:
                    n,d=simplest(l,S,right,S)
                    assert l*d<=n*S<=right*d
                    if d<=bound:
                        u=sixth(d)
                        if U<=u<=V and u%2:
                            direct(p,u,n)
                            tests+=1
                    continue
                m=isqrt(U*V)
                assert U<=m<V
                intervals.extend(((U,m),(m+1,V)))
    print('Prime exponents:',count)
    print('Integer root intervals checked:',boxes)
    print('Direct monotone checks in the original equation:',tests)
    print('Remaining primitive candidates: 0')


if __name__=='__main__':run()
