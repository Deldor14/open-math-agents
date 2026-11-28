"""Integrate all piecewise-affine profiles exactly in Q(sqrt(2))."""
from fractions import Fraction as Q
from verifica_parametro import Surd, R, q, ell, rr, Cell, half

zero,one=Surd(0),Surd(1)
a,b=q*(1-R),q*R
cut=2*R-half
assert 0<cut<R<half and 2*a*R>half and a<1
assert ell(R)+rr(R)==half and rr(R)>0 and ell(R)>0
def segment_crossings(nodes,left,right):
    out=set(nodes)
    for u,v in zip(nodes,nodes[1:]):
        x,y=left(u)-right(u),left(v)-right(v)
        if x*y<0:
            out.add(u+(v-u)*x/(x-y))
    return sorted(out)
def primary_c(u): return min(half-ell(u), a*(half+u))
def primary_d(u): return min(half-rr(u), ell(u)+b*half)
def span(u): return primary_d(u)-rr(u)
def pos(u): return min(primary_c(u),(1-span(u))/2)
def neg(u): return max(ell(u),span(u)/2)
def width(u): return pos(u)-rr(u)+primary_d(u)-neg(u)

nodes=[zero,cut,R]
nodes=segment_crossings(nodes,lambda u:half-ell(u),lambda u:a*(half+u))
nodes=segment_crossings(nodes,lambda u:half-rr(u),lambda u:ell(u)+b*half)
nodes=segment_crossings(nodes,primary_c,lambda u:(1-span(u))/2)
nodes=segment_crossings(nodes,ell,lambda u:span(u)/2)
# Also introduce every explicit vertex of the original polygon.
from verifica_parametro import J,F,V,G
nodes=sorted(set(nodes+[J,F,V,G]))
for u in nodes:
    assert 0<=rr(u)<=pos(u)<=primary_c(u)<=half
    assert 0<=ell(u)<=neg(u)<=primary_d(u)<=half
    assert width(u)>=max(primary_c(u)-rr(u),primary_d(u)-ell(u))
    if u>=cut:
        assert primary_c(u)==half-ell(u) and primary_d(u)==half-rr(u)
    assert Cell(None,None,'+').edges(half+u)==(rr(u),pos(u))
    assert Cell(None,None,'-').edges(half+u)==(-primary_d(u),-neg(u))
def integrate(nodes,f):
    return sum(((v-u)*(f(u)+f(v))/2 for u,v in zip(nodes,nodes[1:])),zero)
low=integrate([zero,R,Surd(half)],lambda s:min(ell(s),half-rr(s))+rr(s))
area=low+integrate(nodes,width)
assert area==Surd(Q(17,28),Q(-3,14))
print('Upper subintervals:',len(nodes)-1,'total area =',area.a,'+',area.b,'sqrt(2)')
