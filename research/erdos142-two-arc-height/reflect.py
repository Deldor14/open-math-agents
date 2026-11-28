"""Exact certificate for the circular self-convolution of the upper envelope."""
import sys
from itertools import combinations_with_replacement,product
from fractions import Fraction as Q
sys.path.insert(0,sys.argv[1])
from verifica_parametro import Cell,Surd,R,J,F,V,G,q,rr,ell,half
zero=Surd(0)
def endpoints(u):
    C=min(half-ell(u),q*(1-R)*(half+u))
    D=min(half-rr(u),ell(u)+q*R*half)
    return (rr(u),C,-D,-ell(u))
def width(u):
    l,r=Cell(None,None,'+').edges(half+u)
    p,d=Cell(None,None,'-').edges(half+u)
    return r-l+d-p
def split_knots():
    base=sorted({zero,J,F,V,G,2*R-half,R})
    caps=(lambda u:half-ell(u)-q*(1-R)*(half+u),lambda u:half-rr(u)-ell(u)-q*R*half)
    nodes=set(base)
    for f in caps:
        for a,b in zip(base,base[1:]):
            x,y=f(a),f(b)
            if x*y<0:nodes.add(a+(b-a)*x/(x-y))
    base=sorted(nodes)
    for a,b in zip(base,base[1:]):
        sums=lambda u:[x+y for x,y in combinations_with_replacement(endpoints(u),2)]
        sa,sb=sums(a),sums(b)
        for i,j in combinations_with_replacement(range(10),2):
            for k in range(-2,3):
                x,y=sa[i]-sa[j]+k,sb[i]-sb[j]+k
                if x*y<0:nodes.add(a+(b-a)*x/(x-y))
    return sorted(nodes)
def value(e,t):
    ans=zero
    arcs=((e[0],e[1]),(e[2],e[3]))
    for (l,r),(p,d) in product(arcs,repeat=2):
        for k in range(-2,3):
            s=t+k
            ans+=max(zero,min(r,s-p)-max(l,s-d))
    return ans
def verify():
    knots=split_knots();tested=0
    for u in knots:
        e=endpoints(u)
        envelope=e[1]-e[0]+e[3]-e[2]
        need=2*(envelope-width(u))
        vals=[value(e,s) for s in {x+y for x,y in combinations_with_replacement(e,2)}]
        assert min(vals)>=need,(u,min(vals)-need)
        tested+=len(vals)
    area=zero
    pts=(zero,R,Surd(half))
    wlow=lambda u:rr(u)+min(ell(u),half-rr(u))
    for a,b in zip(pts,pts[1:]):area+=(b-a)*(wlow(a)+wlow(b))/2
    for a,b in zip(knots,knots[1:]):area+=(b-a)*(width(a)+width(b))/2
    assert area==Surd(Q(17,28),Q(-3,14))
    print('Exact height subintervals',len(knots)-1,'distinct breakpoint tests (by row)',tested)
    print('Total area:',area.a,'+',area.b,'sqrt(2)')
if __name__=='__main__':verify()
