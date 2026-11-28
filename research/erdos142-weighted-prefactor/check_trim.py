"""Verify the exact angular area loss and carry envelopes for four small trims."""
from fractions import Fraction as Q
import sys
sys.path.insert(0,sys.argv[1])
from verifica_parametro import Cell, F, G, J, R, V, Surd, ell, half, q as b

def run(delta):
    zero=Surd(0)
    knots=sorted({zero,J-delta/2,J,F,V,V+delta/2,G,R})
    def lost(u):
        B=half-2*ell(u)-b*max(zero,V-u)
        slope_gap=b*(max(zero,u-V)+max(zero,u-G))
        deduction=max(zero,b*delta/2-slope_gap)
        assert 2*b*(R-u)-b*max(zero,V-u)-b*max(zero,G-u)==half-slope_gap
        out=zero
        for layer,offset in [('+',-half),('-',half)]:
            low,high=Cell(None,None,layer).edges(half+u)
            elo,ehi=2*low+offset,2*high+offset
            assert ehi<=B
            assert elo<=B-deduction
            if layer=='-':assert ehi==B
            if layer=='+':assert ehi==B-b*max(zero,J-u)
            out+=max(zero,ehi-B+deduction)/2
        return out
    area=sum((y-x)*(lost(x)+lost(y))/2 for x,y in zip(knots,knots[1:]))
    assert area==b*(2*V-J)*delta/4+3*b*delta**2/16
    return area

if __name__=='__main__':
    for denominator in (32,64,128,256):
        loss=run(Q(1,denominator))
        print(denominator,loss.a,loss.b)
