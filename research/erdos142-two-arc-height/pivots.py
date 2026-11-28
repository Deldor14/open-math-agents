"""Exact uniqueness of the reflected minimizer on the open first band."""
from itertools import product,combinations_with_replacement
from fractions import Fraction as Q
import sys
sys.path.insert(0,sys.argv[1])
from verifica_parametro import Surd,R,q,J,half
zero=Surd(0)
X=q*(1-R)/2
Y=q*R/2
def ends(u):
    g=half-q*(R-u)
    return (-g-Y,-g,zero,X)
def traces(u):
    return [a+b for a,b in combinations_with_replacement(ends(u),2)]
def overlap(u,t):
    l,r,p,s=ends(u)
    arcs=[(l,r),(p,s)]
    return sum((max(zero,min(b,t+k-c)-max(a,t+k-d))
                for (a,b),(c,d) in product(arcs,repeat=2) for k in range(-2,3)),zero)
K={zero,J}
t0,t1=traces(zero),traces(J)
for i,j in combinations_with_replacement(range(10),2):
    for k in range(-2,3):
        u,v=t0[i]-t0[j]+k,t1[i]-t1[j]+k
        if u*v<0:K.add(J*u/(u-v))
K=sorted(K)
def same(t,s):return any(t-s==k for k in range(-2,3))
def check(u,strict):
    l,r,_,x=ends(u)
    g=-r
    assert overlap(u,l)==Y-g
    for t in traces(u):
        diff=overlap(u,t)-(Y-g)
        assert diff>=0
        if strict:
            assert (diff==0)==same(l,t)
    if strict:
        assert l/2+half>X and 0<g<Y and Y+g<half
for u in K:check(u,0<u<J)
for a,b in zip(K,K[1:]):check((a+b)/2,True)
B0=J/2-q*J*J/4
print(len(K)-1,'affine height intervals: unique minimizer on 0<u<J.')
print('Forced area',B0.a,'+',B0.b,'sqrt(2).')
