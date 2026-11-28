"""Independent finite tests of line variance, offset shadows, and polygon moments."""
from fractions import Fraction as Q
from itertools import product
from math import comb
from pathlib import Path
import sys

from moments import moments
from verifica_parametro import Cell, F, G, J, R, Surd, V, half

def power(x, exponent):
    ans=Surd(1)
    for _ in range(exponent):
        ans *= x
    return ans

def edge_integral(x0, y0, x1, y1, exponent):
    # Integral of s^(k+1) dt/(k+1) along one oriented straight edge.
    value=Surd(0)
    for j in range(exponent+2):
        value += comb(exponent+1,j)*power(x0,exponent+1-j)*power(x1-x0,j)/(j+1)
    return (y1-y0)*value/(exponent+1)

def check_moments():
    A,mean,var,trim=moments()
    knots=[Surd(0),J,F,V,G,R]
    levels={'L':[Surd(0),R,Surd(half)],'+':[half+j for j in knots],'-':[half+j for j in knots]}
    totals=[Surd(0) for _ in (0,2,4)]
    for name,heights in levels.items():
        for left,right in zip(heights,heights[1:]):
            chart=Cell(left,right,name)
            lo,hi=chart.edges(left)
            endlo,endhi=chart.edges(right)
            pts=[(left,lo),(right,endlo),(right,endhi),(left,hi)]
            for j,e in enumerate((0,2,4)):
                totals[j]+=sum((edge_integral(*s,*t,e) for s,t in zip(pts,pts[1:]+pts[:1])),Surd(0))
    assert totals==[A,A*mean,A*(var+mean*mean)]
    assert trim==Surd(Q(39,14),Q(25,42))
    assert var==Surd(Q(90096431777,1648424845620),-Q(4064326319,366316632360))

def check_lines(p):
    points=list(product(range(p),repeat=2))
    Qg=len(points)
    bins=((lambda x:(x[0]*x[1])%p),(lambda x:(x[1]**2+x[0]+1)%p))
    cases=0
    for chart in bins:
        for times in (list(range(p)),[0,1],list(range(0,p,2))):
            sizes=[sum(chart(x)==j for x in points) for j in range(p)]
            variances=[0]*p
            for d,b in product(points,repeat=2):
                counts=[0]*p
                for i in times:
                    x=tuple((bi+i*di)%p for bi,di in zip(b,d))
                    counts[chart(x)]+=1
                for j,count in enumerate(counts):
                    variances[j]+=(Qg*count-len(times)*sizes[j])**2
            assert variances==[Qg**2*len(times)*h*(Qg-h) for h in sizes]
            cases+=len(sizes)
    return cases

def check_boxes():
    p=17
    grid=list(product(range(p),repeat=2))
    box=set(product((p-1,0,1),repeat=2))
    diffs={((x[0]-y[0])%p,(x[1]-y[1])%p) for x,y in product(box,repeat=2)}
    checked=0
    offsets=((0,0),(3,7))
    for d in grid:
        for length in (2,3,4):
            if any(tuple((i*v)%p for v in d) in diffs for i in range(1,length)):
                continue
            for b in offsets:
                shadow={tuple((b[j]+i*d[j]+u[j])%p for j in (0,1))
                        for i in range(length) for u in box}
                assert len(shadow)==length*len(box)
                checked+=1
    return checked

if __name__=='__main__':
    check_moments()
    print('Exact oriented-boundary moments and area derivative agree.')
    print('Histogram bin/interval variance identities:',sum(check_lines(p) for p in (3,5,7)))
    print('Disjoint offset shadows:',check_boxes())
