"""Exact interval certificate for the two disjoint families of charged rows."""
import sys
from fractions import Fraction as Q
sys.path.insert(0,sys.argv[1])
from verifica_parametro import Surd, Cell, R, J, F, V, G, q, rr, ell, half

zero=Surd(0)
quarter=Q(1,4)
a=q*(1-R)
b=q*R

def width(u):
    p,P=Cell(None,None,'+').edges(half+u)
    n,N=Cell(None,None,'-').edges(half+u)
    return P-p+N-n

def original_caps(u):
    return min(half-ell(u),a*(half+u)),min(half-rr(u),ell(u)+b/2)

def knot_check(u):
    w=half-ell(u)-rr(u)
    assert w==q*(R-u) and w>=0
    C,D=original_caps(u)
    pos_budget=half-ell(u)-C
    neg_budget=half-rr(u)-D
    assert pos_budget==q*max(zero,F-u)
    assert neg_budget==q*max(zero,G-u)
    if J<=u<=V:
        assert width(u)==half
    if V<=u<=G:
        assert width(u)==C-rr(u)+D-ell(u)
    if u>=G:
        assert width(u)==2*w

assert zero<J<F<V<G<quarter<R<half
assert G<quarter and quarter+J<G+V and 2*G==R
assert R-half+V>0 and R-half+G<R
nodes=sorted({zero,J,F,V,G,R})
for t in nodes:
    knot_check(t)
for lo,hi,offset in [(zero,J,quarter),(V,G,G)]:
    for u in (lo,hi):
        v=u+offset
        x=2*v-half-u
        assert 0<=x<R and G<=v<=R
        assert 2*rr(v)==a*(half+u)+rr(x)
        assert 1-2*ell(v)==1-(ell(u)+b/2)-ell(x)
        right_cap,left_cap=original_caps(u)
        pos_budget=half-ell(u)-right_cap
        neg_budget=half-rr(u)-left_cap
        W=1-2*ell(v)-2*rr(v)
        assert pos_budget+neg_budget<=W
        if offset==quarter:
            assert pos_budget+neg_budget==W
        else:
            assert pos_budget==0 and 2*neg_budget==W
area=sum(((v-u)*(width(u)+width(v))/2 for u,v in zip(nodes,nodes[1:])),zero)
low=lambda u:rr(u)+min(ell(u),half-rr(u))
for lo,hi in [(zero,R),(R,half)]:
    area+=(hi-lo)*(low(lo)+low(hi))/2
assert area==Surd(Q(17,28),Q(-3,14))
print('Both unit-slope row maps verified. Disjoint target bands, exact budget inequalities.')
print('Central width 1/2. Full upper tail width 2q(R-u).')
print('Sharp area with unrestricted upper support:',area.a,'+',area.b,'sqrt(2).')
