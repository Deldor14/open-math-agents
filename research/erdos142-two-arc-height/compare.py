"""Pointwise exact comparison of both orientations and the disjoint-fold bound."""
import sys
from fractions import Fraction as Q
sys.path.insert(0,sys.argv[1])
from verifica_parametro import Surd, Cell, R, J, F, V, G, rr, ell, q, half
zero=Surd(0);alpha=q*(1-R);coef=q*R
def split(nodes,left,right):
    out=set(nodes)
    for a,b in zip(nodes,nodes[1:]):
        f,g=left(a)-right(a),left(b)-right(b)
        if f*g<0:out.add(a+(b-a)*f/(f-g))
    return sorted(out)
xl=lambda u:half-ell(u)
xr=lambda u:alpha*(half+u)
yl=lambda u:half-rr(u)
yr=lambda u:ell(u)+coef*half
C=lambda u:min(xl(u),xr(u))
D=lambda u:min(yl(u),yr(u))
nodes=sorted({zero,R,J,F,V,G,2*R-half})
nodes=split(split(nodes,xl,xr),yl,yr)
profiles=[]
for lo,n,hi,cap in ((rr,ell,C,D),(ell,rr,D,C)):
    def scores(u,lo=lo,n=n,hi=hi,cap=cap):
        delta=cap(u)-lo(u)
        return delta+min(hi(u),(1-delta)/2)-max(n(u),delta/2)
    nodes=split(nodes,hi,lambda u:(1-cap(u)+lo(u))/2)
    nodes=split(nodes,n,lambda u:(cap(u)-lo(u))/2)
    profiles.append(scores)
Ilo=lambda u:2*rr(u)-half
Ihi=lambda u:2*C(u)-half
Klo=lambda u:half-2*D(u)
Khi=lambda u:half-2*ell(u)
nodes=split(split(nodes,Ilo,Klo),Ihi,Khi)
for u in nodes:
    positive=Cell(None,None,'+').edges(u+half)
    negative=Cell(None,None,'-').edges(u+half)
    best=profiles[0](u)
    assert best==positive[1]-positive[0]+negative[1]-negative[0]
    assert best>=profiles[1](u)
    assert best>=C(u)-rr(u) and best>=D(u)-ell(u)
    assert best>=(max(Ihi(u),Khi(u))-min(Ilo(u),Klo(u)))/2
def integrate(xs,fn):
    return sum((b-a)*(fn(a)+fn(b))/2 for a,b in zip(xs,xs[1:]))
area=integrate([zero,R,Surd(half)],lambda x:rr(x)+min(ell(x),half-rr(x)))+integrate(nodes,profiles[0])
assert area==Surd(Q(17,28),Q(-3,14))
print('Compared both orientations, single lobes and disjoint lifts over',len(nodes)-1,'affine intervals.')
print('Area',area.a,'+',area.b,'sqrt(2)')
