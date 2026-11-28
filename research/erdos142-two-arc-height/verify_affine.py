"""Exact verification of angular-capacity reduction and a switched rational polygon."""
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import sys

half=Q(1,2)
quarter=Q(1,4)
zero=Q(0)

def positive(x):
    return max(zero,x)

def cap(alpha,beta,z):
    X,Y=min(z,alpha),min(z,beta)
    g=half-z
    h=1-g-X-Y
    loss=min(2*Y,positive(X+Y+g-h),positive(X-h)+positive(Y-g))
    return X+Y-loss/2

def excess(alpha,beta,z):
    X,Y=min(z,alpha),min(z,beta)
    return positive(min(X+Y-z,quarter+X+Y/2-3*z/2,half-z))

def surplus_integral(alpha,beta,Z):
    # Height slices; the extra Z-y constraint handles an early truncation.
    B=min(beta,quarter)
    K=min(alpha+beta,half)
    lines=[(Z,-1),(K,-2),((half+2*alpha+beta)/3,Q(-5,3))]
    knots={zero,B}
    for c,m in lines:
        knots.add(min(B,max(zero,-c/m)))
    for (c,m),(d,n) in combinations(lines,2):
        knots.add(min(B,max(zero,(d-c)/(m-n))))
    knots=sorted(knots)
    height=lambda y: positive(min(c+m*y for c,m in lines))
    return sum((v-u)*(height(u)+height(v))/2 for u,v in zip(knots,knots[1:]))

def closed(alpha,beta):
    K=min(half,alpha+beta)
    B=min(quarter,beta)
    d=3*K-half-2*(alpha+beta)+beta
    return K*B-B*B-(positive(d)**2-positive(d-B)**2)/6

def row_integral(alpha,beta,Z):
    # Independent vertical slicing in z, building all the affine branch knots.
    base=sorted({zero,min(Z,beta),min(Z,alpha),Z})
    knots=set(base)
    def branches(z):
        X,Y=min(z,alpha),min(z,beta)
        return (zero,X+Y-z,quarter+X+Y/2-3*z/2,half-z)
    for u,v in zip(base,base[1:]):
        a,b=branches(u),branches(v)
        for i,j in combinations(range(4),2):
            left,right=a[i]-a[j],b[i]-b[j]
            if left*right<0:
                knots.add(u+(v-u)*left/(left-right))
    knots=sorted(knots)
    for z in knots:
        assert cap(alpha,beta,z)-z==excess(alpha,beta,z)
    return sum((v-u)*(cap(alpha,beta,u)-u+cap(alpha,beta,v)-v)/2
               for u,v in zip(knots,knots[1:]))

def check_integrals():
    runs=0
    for i in range(1,17):
        for j in range(1,i+1):
            a,b=Q(i,32),Q(j,32)
            limit=min(half,a+b)
            for p in range(6):
                Z=limit*p/5
                assert row_integral(a,b,Z)==surplus_integral(a,b,Z)
                runs+=1
            assert surplus_integral(a,b,limit)==closed(a,b)
    print(runs,'exact cross-checks of the two slice integrals.')

def rational_polygon():
    # One extreme intercept of the new family. Verify the primary exclusions
    # independently on the projected vertices, using the published geometric routines.
    sys.path.insert(0,str(Path(sys.argv[1]).resolve()))
    from verifica_poligono import projected_vertices,excludes
    alpha,beta=Q(69,224),Q(25,112)
    s=2*(alpha+beta)
    e=zero
    Z=half-e
    R=Z/s
    r=lambda u:2*alpha*u
    l=lambda u:e+2*beta*u
    def expressions(u):
        z=Z-s*u
        X,Y=min(z,alpha),min(z,beta)
        C,D=r(u)+X,l(u)+Y
        d=D-r(u)
        return X,Y,C,D,d
    def values(u):
        X,Y,C,D,d=expressions(u)
        oriented=min(C,(1-d)/2)-r(u)+D-max(l(u),d/2)
        return oriented,Z-s*u
    cuts=sorted({zero,R,*[(Z-x)/s for x in (alpha,beta) if zero<x<Z]})
    def extend(knots,func):
        out=set(knots)
        for u,v in zip(knots,knots[1:]):
            x,y=func(u),func(v)
            if x*y<0:
                out.add(u+(v-u)*x/(x-y))
        return sorted(out)
    def upper_cut(u):
        X,Y,C,D,d=expressions(u)
        return 2*C+d-1
    def lower_cut(u):
        X,Y,C,D,d=expressions(u)
        return 2*l(u)-d
    cuts=extend(extend(cuts,upper_cut),lower_cut)
    cuts=extend(cuts,lambda u:values(u)[0]-values(u)[1])
    class Cell:
        def __init__(self,a,b,layer,mode):
            self.a,self.b,self.layer,self.mode=a,b,layer,mode
        def edges(self,x):
            if self.layer=='L':
                return -min(l(x),half-r(x)),r(x)
            u=x-half
            X,Y,C,D,d=expressions(u)
            if self.mode=='semicircle':
                z=Z-s*u
                return (r(u),C) if self.layer=='+' else (-l(u)-(z-X),-l(u))
            return (r(u),min(C,(1-d)/2)) if self.layer=='+' else (-D,-max(l(u),d/2))
    cells=[Cell(zero,R,'L','lower'),Cell(R,half,'L','lower')]
    for u,v in zip(cuts,cuts[1:]):
        mid=(u+v)/2
        base,z=values(mid)
        mode='oriented' if base>=z else 'semicircle'
        for sign in ('+','-'):
            cell=Cell(half+u,half+v,sign,mode)
            cells.append(cell)
        for t in (u,v):
            lo,hi=cells[-2].edges(half+t)
            n,N=cells[-1].edges(half+t)
            assert -half<=n<=N<=0<=lo<=hi<=half
            assert N-n+hi-lo==cap(alpha,beta,Z-s*t)
            if mode=='semicircle':
                assert hi-n<=half
            else:
                assert -n<=lo-2*N and -n+2*hi<=1+lo
    assert any(c.mode=='semicircle' for c in cells)
    exclusions=0
    for x,y,z in product(cells,repeat=3):
        vv=projected_vertices(x,y,z)
        if vv:
            for k in (-1,0,1):
                excludes(x,y,z,vv,k)
                exclusions+=1
    area=zero
    for c in cells:
        l0,h0=c.edges(c.a)
        l1,h1=c.edges(c.b)
        area+=(c.b-c.a)*(h0-l0+h1-l1)/2
    assert area==quarter+closed(alpha,beta)/s==Q(579,1904)
    print('Rational switched polygon:',len(cells),'cells,',exclusions,
          'primary tests, area',area,'with lower intercept zero.')

if __name__=='__main__':
    check_integrals()
    rational_polygon()
