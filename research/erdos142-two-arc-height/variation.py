"""Exact signs and first moments of both concave first-variation kernels."""
from fractions import Fraction as Q
import sys
sys.path.insert(0,sys.argv[1])
from verifica_parametro import Surd, R, J, V, G, F, half
zero=Surd(0)
T=2*R-half
plus=[(zero,J,half),(J,V,1),(G,R,-1),(T-J,T,-1)]
minus=[(zero,V,1),(V,R,-1),(T-J,T,-half),(T-G,T-V,-1)]
assert zero<F==T-G<V<T-V<G<T-J<T<R
for label,terms in [('right',plus),('left',minus)]:
    xs=sorted({zero,R,V}|{a for lo,hi,c in terms for a in (lo,hi)})
    weighted=sum((c*(hi-lo)*(R-(lo+hi)/2) for lo,hi,c in terms),zero)
    assert weighted==0
    for lo,hi in zip(xs,xs[1:]):
        v=(lo+hi)/2
        val=sum(c for i,j,c in terms if i<v<j)
        assert val>=0 if v<V else val<=0
    print(label,len(xs)-1,'constant pieces, one sign change, affine moment exactly zero.')
