"""Exact affine checks; takes the directory of the published oriented polygon."""
import sys
sys.path.insert(0,sys.argv[1])
from verifica_parametro import Surd, J, V, G, F, R, q, half, Cell, rr, ell

def ends(u):
    l,h=Cell(None,None,'+').edges(half+u)
    m,n=Cell(None,None,'-').edges(half+u)
    return (2*l-half,2*m+half,2*h-half,2*n+half)

def check():
    assert 0<J<F<V<G<R
    knots=[Surd(0),J,F,V]
    area=Surd(0)
    for u in knots:
        a,b,c,d=ends(u)
        assert a<b<c<=d
        assert a==2*rr(u)-half and b==a+2*q*(G-u)
        assert d==(a+b)/2+half and c==d-q*max(J-u,Surd(0))
        assert (a+b)/2<a+half<(c+d)/2
    for u,v in zip(knots,knots[1:]):
        a,b,c,d=ends(u);aa,bb,cc,dd=ends(v)
        area+=(v-u)*((c-a+d-b)+(cc-aa+dd-bb))/4
        mid=(u+v)/2
        # Both endpoints lie in the open cells and lift to a negative midpoint.
        h=(v-u)/128
        a,b,c,d=ends(mid)
        am,_,cm,_=ends(mid-h)
        _,bp,_,dp=ends(mid+h)
        ex,ez=am+q*h/2,bp+q*h/2
        ey=d-q*h/2
        assert am<ex<cm and bp<ez<dp and b<ey<d
        assert (ex+ez)/2+half==ey
    assert area==V/2-q*J*J/4
    print('All endpoint inequalities, carry signs and area passed in Q(sqrt(2)).')
    print('Exceptional area:',area.a,'+',area.b,'sqrt(2)')
if __name__=='__main__':check()
