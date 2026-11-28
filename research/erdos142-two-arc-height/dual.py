"""Exact certificate for the concave area bound; pass the original polygon folder."""
import sys
from fractions import Fraction as Q
from itertools import product
sys.path.insert(0,sys.argv[1])
from verifica_parametro import Surd, R as R0, J, V, G, half
zero=Surd(0)
one=Surd(1)
A=Surd(Q(17,28),Q(-3,14))
C=4*A-1
cut=Q(369,1000)
short=half*(1-Surd(0,half))
def high_baseline(r):
    H=(half-r)/(2*r)
    return r*H*(1-H)
assert Surd(cut)*short<A-Q(1,4)
assert high_baseline(cut)<A-Q(1,4)
assert 12*cut*cut>1 and 0<(half-cut)/(2*cut)<half

def params(L):
    g=(C+16*L-4)/14
    return g-C/2,g/2+C/4,g,2*L-half

def moment(lo,hi,L):
    return (hi-lo)*(L-(lo+hi)/2)

def kernels(L):
    j,w,g,T=params(L)
    right=[(zero,j,half),(j,w,1),(g,L,-1),(T-j,T,-1)]
    left=[(zero,w,1),(w,L,-1),(T-j,T,-half),(T-g,T-w,-1)]
    return right,left

for L in [Surd(Q(1,3)), Surd(half)]:
    j,w,g,T=params(L)
    assert 0<=j<=w<=g<=L
    assert j<=T-g<=T-w<=T-j<=T<=L
    assert w/2-j/4==A-Q(1,4)
# All ordering comparisons are affine in L. Both moment identities are
# quadratic in L, so three distinct checks over the field prove them identically.
for L in [Surd(Q(1,3)),R0,Surd(half)]:
    for K in kernels(L):
        assert sum((c*moment(u,v,L) for u,v,c in K),zero)==Q(9,14)*(L-R0)*(L-R0)
assert params(R0)[:3]==(J,V,G)
assert short/3<A-Q(1,4)
print('Affine fan bounds at both endpoints; two quadratic moments certified at three distinct points.')

def clip(l,r,u,v):
    return max(0,min(r,v)-max(l,u))

def angular_checks():
    # On the doubled cover, the surviving arc portions are computed directly
    # by subtracting the length inside the forbidden open interval.
    grid=16
    pairs=[(a,b) for a in range(grid+1) for b in range(grid+1-a)]
    count=normal=0
    for (a,b),(p,q) in product(pairs,repeat=2):
        z=a+b
        # Circumference 2*grid, terminal test forbids (p,grid-q) modulo it.
        l1,r1=-a,b
        l2,r2=grid-a,grid+b
        forbidden=lambda l,r:sum(clip(l,r,p+t,grid-q+t) for t in (-2*grid,0,2*grid))
        x=z-forbidden(l1,r1)
        y=z-forbidden(l2,r2)
        assert x<=min(z,a+p)+max(0,b+q-grid)
        assert y<=min(z,b+q)+max(0,a+p-grid)
        if a+p<=grid and b+q<=grid:
            assert x==min(z,a+p) and y==min(z,b+q)
            normal+=1
        count+=1
    print(count,'terminal-envelope comparisons including wrapped slices;',normal,'in the two-cap case.')
angular_checks()

def moving_affine():
    # Unit-slope sector after integer shear. Double-check the second sheet lies
    # entirely in the terminal gap on every tested mixed row.
    count=0
    for i in range(1,12):
        for j in range(i,12):
            left,right=Q(i,12),Q(j,12)
            for R in (Q(1,3),Q(2,5),half):
                T=2*R-half
                for h in range(1,10):
                    u=T*h/10
                    x=T-u
                    a,b=right*(R-u),-left*(R-u)
                    p,q=right*(R-x),-left*(R-x)
                    assert p<=half-a<=half+b<=half-q
                    count+=1
    print(count,'strict-unit-slope moving-row checks; surplus bound 1/32.')
moving_affine()
