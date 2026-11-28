"""Exact moments and first area variation for the polygon in note 163553.

Pass the directory containing the two original polygon-verification modules.
"""
from fractions import Fraction
from pathlib import Path
import sys

source = Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent
sys.path.insert(0, str(source.resolve()))
from verifica_parametro import Cell, F, G, J, R, Surd, V, half

def power(x, k):
    value = Surd(1)
    for _ in range(k):
        value *= x
    return value

def strip_moment(cell, exponent):
    left, right = cell.a, cell.b
    y0, y1 = cell.edges(left)
    z0, z1 = cell.edges(right)
    width0, width1 = y1-y0, z1-z0
    assert width0 >= 0 and width1 >= 0 and width0 + width1 > 0
    slope = (width1-width0)/(right-left)
    intercept = width0-slope*left
    def primitive(s):
        return intercept*power(s,exponent+1)/(exponent+1) + slope*power(s,exponent+2)/(exponent+2)
    return primitive(right)-primitive(left)

def width(layer, s):
    low,high = Cell(None,None,layer).edges(s)
    return high-low

def moments():
    lower=[Surd(0),R,Surd(half)]
    upper=[half+u for u in (Surd(0),J,F,V,G,R)]
    cells=[Cell(left,right,layer) for layer,knots in [('L',lower),('+',upper),('-',upper)]
           for left,right in zip(knots,knots[1:])]
    area,second,fourth=[sum((strip_moment(cell,e) for cell in cells),Surd(0)) for e in (0,2,4)]
    assert area==Surd(Fraction(17,28),Fraction(-3,14))
    mean=second/area
    variance=fourth/area-mean*mean
    assert variance>0
    trim=1+4*R+sum((width(layer,Surd(half)) for layer in ('L','+','-')),Surd(0))
    return area,mean,variance,trim

if __name__=='__main__':
    from math import exp,pi,sqrt
    values = moments()
    def dec(z):
        return float(z.a)+sqrt(2)*float(z.b)
    for name,z in zip(('A','E[s²]','variance(s²)','κ'),values):
        print(name, '=', z.a,'+',z.b,'√2', '≈',dec(z))
    a,mean,var,kappa=map(dec,values)
    constant=exp(-kappa/(128*a))/(2**23*sqrt(2*pi*var))
    print('typical-direction coefficient ≈',constant)
