"""Cross-check the local-curvature features independently and the single-lift geometry."""
import argparse
from fractions import Fraction as Q
from math import floor, log2, sqrt
from pathlib import Path
from random import Random
import sys
from curved import CurvedTable

def verify(path):
    sys.path.insert(0,str(Path(path).resolve()))
    from verifica_parametro import J,V,G,Cell,Surd,q,half,rr
    def real(x):
        x=Surd.lift(x)
        return float(x.a)+sqrt(2)*float(x.b)
    rng=Random(609)
    mesh=200000
    grid=CurvedTable(80,mesh)
    lo,hi=real(J),real(V)
    def true_height(i,j):
        s=i/mesh; t=j/mesh-(2*j>=mesh); u=s-.5
        e=t if s<.5 else 2*t+(.5 if t<0 else -.5)
        v=e-2*real(rr(Q(i,mesh)-half))+.5
        w=max(0,-u,u-hi); reserve=0.
        for k in range(64):
            a=hi-(hi-lo)*2**-k; b=hi-(hi-lo)*2**(-k-1); z=(a+b)/2
            reserve+=2*(max(0,u-a)**2-max(0,u-b)**2)+4*(b-a)*max(0,u-z)
            if a<u<b: w=min(u-a,b-u)
        if u<0: lam,g,x=5/8,6,e-1/32
        elif u>hi: lam,g,x=5/2,7/8,e+.5
        elif u>lo: lam,g,x=3/4,.5,e+.5
        else: lam,g,x=0,0,e
        den=1-g*x*x
        bend=max(0,u)**2-max(0,u-lo)**2
        phi=.01*s*s+.99*bend+.34*s+.75*reserve+lam*w*w/den
        height=grid.K*phi+(e*e if u<0 else (v-.25)**2)
        height+=8/float(grid.tau)*sum(max(0,s-real(z)) for z in grid.cusps)
        qscore=10 if not lam else max(1,grid.H*w*sqrt(lam*g*(lam+.01)/.01)/den**1.5)
        if u>0 and t>0 and u<real(G) and float(grid.tau)+64/mesh<v<2*real(q)*(real(G)-u)-float(grid.tau)-64/mesh:
            qscore*=2
        return mesh*height,grid.m**2*log2(qscore)
    count=single=0; bands=set()
    points=[(rng.randrange(mesh),rng.randrange(mesh)) for _ in range(90)]
    for u in [Q(1,25),Q(11,100),Q(3,25),Q(13,100),Q(3,20),Q(18,100),Q(22,100)]:
        points += [(int(mesh*(half+u)),j) for j in range(1000,mesh//2,6000)]
    for i,j in points:
        result=grid.at(i,j)
        if result is None: continue
        s=Q(i,mesh); u=s-half; t=Q(j if 2*j<mesh else j-mesh,mesh)
        height,score=true_height(i,j)
        if abs(height-round(height))>1e-5: assert result[0]==floor(height)
        if abs(score-round(score))>1e-8 or score==0: assert result[1]==floor(score)
        assert result[2]==(Q(54,100)<s<Q(55,100) and Q(12,100)<t<Q(13,100))
        bands.add('L' if u<0 else 'B' if u<J else 'P' if u<V else 'U')
        if 0<u<G and t>0 and grid.tau+Q(64,mesh) < 2*t-2*rr(u) < 2*q*(G-u)-grid.tau-Q(64,mesh):
            single+=1
        count+=1
    assert bands=={'L','B','P','U'} and single>0,(bands,single,grid.H)
    # Test at all affine breakpoints by taking the two limits on each piece.
    # The negative folded lower endpoint stays at or above 2g, and the positive
    # upper endpoint reaches 2g throughout the strip before the source trims.
    knots=sorted(set([Surd(0),J,(J+V)/2,V,G]+grid.knots))
    tests=0
    for a,b in zip(knots,knots[1:]):
        if b>G: continue
        mid=(a+b)/2
        plateau=next((l for l,r in grid.plateaus if l<mid<r),None)
        for u in (a,b):
            if grid.knots[-1]<mid<V: continue
            delta=q*(u-plateau) if plateau is not None else Surd(0)
            negative=Cell(None,None,'-').edges(half+u)[0]+delta
            positive=Cell(None,None,'+').edges(half+u)[1]+delta/2
            assert 2*negative+1-2*rr(u)>=2*q*(G-u)
            assert 2*positive-2*rr(u)>=2*q*(G-u)
            tests+=2
    print(count,'feature rows over all four bands,',single,'single-lift credits,',tests,'exact edge comparisons')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('geometry')
    verify(p.parse_args().geometry)
