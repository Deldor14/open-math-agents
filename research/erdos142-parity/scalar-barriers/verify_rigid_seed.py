"""Exact two-way mixed-radix count and finite interval proof below F104/F103."""
from collections import Counter
from fractions import Fraction
from math import prod

def fibonacci(n):
    a,b=0,1
    for _ in range(n):
        a,b=b,a+b
    return a

def seed():
    widths=[30]*3+[31]*9
    target=459
    ways=[1]+[0]*target
    # Both alphabet sizes use the same half-integer center.
    radix=1<<prod(widths).bit_length()
    packed=1
    for d in widths:
        charge=Counter(((2*j-29)**2-1)//8 for j in range(d))
        ways=[sum(h*ways[n-j] for j,h in charge.items() if j<=n) for n in range(target+1)]
        packed*=sum(h*radix**j for j,h in charge.items())
    count=ways[target]
    assert count==(packed//radix**target)%radix==2_303_115_151_489_024
    return count,prod(2*d-1 for d in widths)

def verify():
    s=51
    C,mod=seed()
    u,v=fibonacci(103),fibonacci(104)
    d=2*v
    K=64*d
    a,b=K-1,K-d
    start=a
    assert 0<b<a and C>2**s
    E=0
    comparisons=0
    for i in range(s):
        A,B=a+b,a+2*b+1
        if i:
            assert a<b<=A
            low,high=2*A-B,B-A
            x,m=a,0
            while x<b:
                y=min(b,2*x-low,(high+x)//2)
                assert x<y<=b and y+A-x+max(y,A-x)<=B
                x,m=y,m+1
            E=(2*E+1)*m
            comparisons+=m
        a,b=A,B
    assert a*v-b*u==d-v>0
    assert mod*(start+1)<=b
    gain=Fraction(C-2**s,C*E+2**s)
    power=len(str((2*gain.denominator+gain.numerator-1)//gain.numerator))
    assert gain>=Fraction(2,10**power)
    assert 3*10**(2*power)>=a
    print('Strictly below F104/F103:',Fraction(b,a))
    print('Seed cardinality and modulus:',C,mod)
    print('Comparisons:',comparisons,'gain 10^(-%d), n >= 3*10^%d'%(power,2*power))
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must be enabled')
    verify()
