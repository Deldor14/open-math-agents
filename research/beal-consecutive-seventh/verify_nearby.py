"""Exact certificate for primitive septic pairs with gap at most one million."""
from fractions import Fraction
from math import factorial, gcd, isqrt
from verify_septic import convergents, integer_root, prime_exponents, P_MAX

GAP = 10**6
S = 1 << 640
N = 128
ERR = 300
ll = sum((Fraction(2, (2*j+1)*3**(2*j+1)) for j in range(225)), Fraction())
lh = ll + Fraction(3,3**451)
L = int(S*ll)
assert L == int(S*lh)
assert factorial(N+1)>S
assert 4*ERR*(12*P_MAX*GAP)**12<S
assert 4*63*GAP**2<11*23**10


def alpha(p):
    arg=6*L//p
    assert 2*arg<S
    z=term=S
    for k in range(1,N+1):
        term=term*arg//(S*k)
        if not term:break
        z+=term if k%2==0 else -term
    return z


def ceildiv(x,y):
    return -(-x//y)


def radius_denominator(u,p):
    # Replacing p in the power by min(p,160) only widens the interval.
    return p*u**(2*min(p,160)-6)


def check_gap(u,v,p):
    D=u**p
    left=64*v**p
    def right(h):
        h2=h*h
        return D**6 + 21*D**4*h2 + 35*D**2*h2*h2 + 7*h2**3
    lo,hi=1,min(GAP,D-1)
    while lo<hi:
        m=(lo+hi)//2
        if right(m)<left:lo=m+1
        else:hi=m
    if right(lo)==left and lo%2 and gcd(u,lo)==1:
        raise AssertionError((p,u,v,lo))


def inside(v,y,z,R):
    return (z-ERR)*y < S*v and (S*v-(z+ERR)*y)*R <= S*63*GAP**2


def run():
    cfcount=goodden=test_cf=test_small=0
    for p in prime_exponents():
        z=alpha(p)
        for v,y in convergents(z,S,(12*p*GAP)**6):
            cfcount+=1
            if y<23**6 or y%2==0:continue
            a=isqrt(y)
            if a*a!=y:continue
            u=integer_root(a,3)
            if u**6!=y:continue
            goodden+=1
            if inside(v,y,z,radius_denominator(u,p)):
                check_gap(u,v,p)
                test_cf+=1
        for u in range(3,23,2):
            y=u**6
            R=radius_denominator(u,p)
            vmin=max(1,((z-ERR)*y)//S)
            vmax=min(y,ceildiv((z+ERR)*y*R+S*63*GAP**2,S*R))
            for v in range(vmin,vmax+1):
                if inside(v,y,z,R) and gcd(v,u)==1:
                    check_gap(u,v,p)
                    test_small+=1
    print('All odd gaps 1 through',GAP)
    print('Exponents checked:',len(prime_exponents()))
    print('Convergents:',cfcount)
    print('Odd sixth-power denominators u>=23:',goodden)
    print('Exact increasing-polynomial checks (large roots / small roots):',test_cf,test_small)
    print('Remaining primitive candidates: 0')


if __name__=='__main__':run()
