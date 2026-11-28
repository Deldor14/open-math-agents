"""Verify both exponential coefficients by exact positive-series remainders."""
from fractions import Fraction as Q

def log_reciprocal(area, terms=72):
    t=(1-area)/(1+area)
    power=t
    partial=Q(0)
    for j in range(terms):
        partial+=2*power/(2*j+1)
        power*=t*t
    return partial, partial+2*power/((2*terms+1)*(1-t*t))

def main():
    rho=Q(17063783,100663296)
    assert Q(2*98713058+75594412,4*96*2048**2)==rho
    lo,hi=log_reciprocal(rho)
    assert Q(2175514026,10**9)**2<Q(8,3)*lo
    assert Q(8,3)*hi<Q(2175514027,10**9)**2
    a,b=Q(14142135623,10**10),Q(14142135624,10**10)
    assert a*a<2<b*b
    area_lo,area_hi=(17-6*b)/28,(17-6*a)/28
    assert rho*rho>area_hi**3
    assert Q(2182116,10**6)**2<4*log_reciprocal(area_hi)[0]
    assert 4*log_reciprocal(area_lo)[1]<Q(2182117,10**6)**2
    print('2.175514026 < new coefficient < 2.175514027; 2.182116 < planar coefficient < 2.182117.')

if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled.')
    main()
