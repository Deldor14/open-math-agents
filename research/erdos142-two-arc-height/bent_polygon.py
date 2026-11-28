"""Independent exact polygon attaining A with two additional lower bending points."""
import sys
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
sys.path.insert(0,sys.argv[1])
from verifica_parametro import Surd, Cell as Original, R as R0, q as speed, J,F,V,G,half
from verifica_poligono import projected_vertices,excludes
zero=Surd(0)
c=Q(1,64)
m,n=speed*(1-R0),speed*R0
R=R0+c
pos=lambda x:max(zero,x)
def a(u):
    return m*pos(R-u)+pos(c-u)/5+pos(c/2-u)/7
def b(u):
    return n*pos(R-u)+pos(c/3-u)/4
t0=a(zero)
shift=t0-m*R0
assert t0+b(zero)<half
@dataclass
class Cell:
    a:object
    b:object
    layer:str
    mode:str
    def edges(self,s):
        if self.layer=='L':
            return t0-half+b(s),t0-a(s)
        u=s-half
        if self.mode=='semicircle':
            A,B=a(u),b(u)
            if self.layer=='+':
                return t0-A,t0-A+m/2
            return t0-half+B-(A+B-m/2),t0-half+B
        l,r=Original(None,None,self.layer).edges(s-c)
        return shift+l,shift+r
knots=[zero,Surd(c/3),Surd(c/2),Surd(c)]
cells=[Cell(l,r,'L','lower') for l,r in zip(knots+[R],knots[1:]+[R,Surd(half)])]
for sign in ('+','-'):
    for l,r in zip(knots,knots[1:]):
        cells.append(Cell(half+l,half+r,sign,'semicircle'))
    points=[half+c+v for v in (zero,J,F,V,G,R0)]
    for l,r in zip(points,points[1:]):
        cells.append(Cell(l,r,sign,'oriented'))
area=zero
for h in cells:
    lo,hi=h.edges(h.a); ll,hh=h.edges(h.b)
    assert -half<=lo<=hi<=half and -half<=ll<=hh<=half
    area+=(h.b-h.a)*(hi-lo+hh-ll)/2
assert area==Surd(Q(17,28),Q(-3,14))
for l,r in zip(knots,knots[1:]):
    p=Cell(l+half,r+half,'+','semicircle')
    k=Cell(l+half,r+half,'-','semicircle')
    for u in (l,r):
        assert p.edges(half+u)[1]-k.edges(half+u)[0]==half
nprimary=nsecondary=0
for x,y,z in product(cells,repeat=3):
    vs=projected_vertices(x,y,z)
    if vs:
        for k in (-1,0,1):
            excludes(x,y,z,vs,k)
            nprimary+=1
    l,r=max(x.a,y.a,z.a),min(x.b,y.b,z.b)
    if r<=l or y.mode!='oriented':
        continue
    offset=lambda t: -half if t.layer=='+' else half
    for k in (-1,0,1):
        if 2*k+offset(x)+offset(z)-2*offset(y)<0:
            excludes(x,y,z,[(l,l,l),(r,r,r)],k)
            nsecondary+=1
print(len(cells),'cells;',nprimary,'primary exclusions;',nsecondary,'oriented secondary exclusions.')
print('Early row semicircles and exact area (17-6 sqrt(2))/28 verified.')
