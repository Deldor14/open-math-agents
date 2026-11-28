"""Check the two-lobe envelope obstruction in Q(sqrt(2)) at affine vertices."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import sys
sys.path.insert(0, str(Path(sys.argv[1]).resolve()))
from verifica_parametro import Cell, J, V, half, q

# Provide room to shift the envelope in both directions and evaluate its L2 bound.
L, H = Q(15,128), Q(19,128)
assert J < L < H < V
epsmax = Q(1,65536)
P, M = Cell(0,0,'+'), Cell(0,0,'-')
def ends(u,eps):
    a,d = P.edges(half+u)
    b,c = M.edges(half+u)
    return a+2*eps,b+2*eps,c-2*eps,d-2*eps

for u,eps in product((L,H),(Q(0),epsmax)):
    a,b,c,d = ends(u,eps)
    assert d == c+half
    assert a < Q(1,8) < Q(1,4) < d
    # Both intervals of integration have fixed positive length.
    for p in (Q(23,64),Q(23,64)+Q(1,512)):
        z = 2*a-p
        assert a < p < d and b < z < c
        assert 1+Q(1,32) < 2*(p-z) < 1+Q(1,2)
    for w in (Q(1,32),Q(1,24)):
        p,z=b+half-w,b+half+w
        assert a < p < z < d
        assert Q(1,32) < 2*(z-p) < half
    # The endpoint functions are affine across F on J<u<V.  The formula
    # for the positive upper edge on this whole interval is controlled by v.
    h=8*eps/q
    u0,u1=u-h,u+h
    assert J < u0 <= u1 < V
    ax,_,_,_ = ends(u0,eps)
    _,bz,_,_ = ends(u1,eps)
    assert ax+bz==2*c and ax+bz+1 == 2*d
    assert half < 2*(ax-bz) < 1-Q(1,32)
print('Exact four-state envelope transitions and integration intervals passed.')
