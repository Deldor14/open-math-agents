"""Certifica il parametro algebrico del blocco orientato in Q(sqrt(2))."""
import sys
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import total_ordering
from itertools import product
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from verifica_poligono import excludes,projected_vertices

@total_ordering
@dataclass(frozen=True)
class Surd:
    a: Q=Q(0)
    b: Q=Q(0)
    def __post_init__(self):
        object.__setattr__(self,'a',Q(self.a));object.__setattr__(self,'b',Q(self.b))
    @staticmethod
    def lift(o):
        if isinstance(o,float): raise TypeError('Usare frazioni esatte')
        return o if isinstance(o,Surd) else Surd(o)
    def __add__(self,o):
        u=self.lift(o);return Surd(self.a+u.a,self.b+u.b)
    __radd__=__add__
    def __neg__(self):return Surd(-self.a,-self.b)
    def __sub__(self,o):return self+-self.lift(o)
    def __rsub__(self,o):return self.lift(o)+-self
    def __mul__(self,o):
        u=self.lift(o);return Surd(self.a*u.a+2*self.b*u.b,self.a*u.b+self.b*u.a)
    __rmul__=__mul__
    def reciprocal(self):
        delta=self.a**2-2*self.b**2
        return Surd(self.a/delta,-self.b/delta)
    def __truediv__(self,o):return self*self.lift(o).reciprocal()
    def __rtruediv__(self,o):return self.lift(o)*self.reciprocal()
    def __eq__(self,o):
        u=self.lift(o)
        return self.a==u.a and self.b==u.b
    def __hash__(self):
        return hash(self.a) if self.b==0 else hash((self.a,self.b))
    def __lt__(self,o):
        d=self-self.lift(o)
        if d.b==0:return d.a<0
        if d.b<0:return d.a<0 or d.a*d.a<2*d.b*d.b
        return d.a<0 and d.a*d.a>2*d.b*d.b
    def __abs__(self):return self if self>=0 else -self

half=Q(1,2); h=Surd(0,Q(1,3)); q=1/(2*h); R=2*(1+h)/7
G=R/2; V=(3-4*h)/7; J=(10*h-4)/7; F=(J+V)/2
def rr(s):return q*(1-R)*s
def ell(s):return half-q*R+q*R*s
def positive(x):return max(Surd(0),x)
@dataclass(frozen=True)
class Cell:
    a:Surd
    b:Surd
    layer:str
    def edges(self,s):
        if self.layer=='L':return -min(ell(s),half-rr(s)),rr(s)
        u=s-half
        f=q*positive(F-u);g=q*positive(G-u);v=q*positive(V-u)/2
        if self.layer=='+':return rr(u),half-ell(u)-max(f,v)
        return -(half-rr(u)-g),-(ell(u)+v)
    def offset(self):return {'L':0,'+':-half,'-':half}[self.layer]
def verify():
    knots=[Surd(0),J,F,V,G,R]
    assert all(a<b for a,b in zip(knots,knots[1:]))
    lower=[Surd(0),R,Surd(half)]
    upper=[half+t for t in knots]
    cells=[Cell(a,b,t) for t,k in [('L',lower),('+',upper),('-',upper)]
           for a,b in zip(k,k[1:])]
    area=Surd(0)
    a1=a2=0
    for cell in cells:
        l0,h0=cell.edges(cell.a); l1,h1=cell.edges(cell.b)
        assert -half <=l0<=h0<=half and -half<=l1<=h1<=half
        assert (h0-l0)+(h1-l1)>0
        assert max(abs(l1-l0),abs(h1-h0)) <= cell.b-cell.a
        if cell.layer=='+':assert min(l0,l1)>=0
        if cell.layer=='-':assert max(h0,h1)<=0
        area+=(cell.b-cell.a)*(h0-l0+h1-l1)/2
    for x,y,z in product(cells,repeat=3):
        vertices=projected_vertices(x,y,z)
        if vertices:
            for k in [-1,0,1]:
                excludes(x,y,z,vertices,k);a1+=1
        a,b=max(x.a,y.a,z.a),min(x.b,y.b,z.b)
        if a>=b:continue
        for k in [-1,0,1]:
            if (1 if x.layer=='L' else 2)*k+x.offset()+z.offset()-2*y.offset()<0:
                excludes(x,y,z,[(a,a,a),(b,b,b)],k);a2+=1
    assert area==Surd(Q(17,28),Q(-3,14)) and area>Q(579,1904)
    print('Area =',area.a,'+',area.b,'* sqrt(2). Esclusioni:',a1,a2)
if __name__=='__main__':verify()
