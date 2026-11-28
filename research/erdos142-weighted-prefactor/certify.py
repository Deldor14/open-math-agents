"""Enclose the real integral constant using directed interval arithmetic.
Usage: python certify.py /path/to/original/erdos142-deterministic-shell [subdivisions].
Requires mpmath, plus the two pinned original polygon source files.
"""
import sys
from fractions import Fraction as Q
from mpmath import iv
sys.path.insert(0,sys.argv[1])
from verifica_parametro import Surd, Cell, R, J, F, V, G, q, half

iv.dps=35
pieces=int(sys.argv[2]) if len(sys.argv)>2 else 512
root2=iv.sqrt(2)
def rational(x):
    return iv.mpf(x.numerator)/x.denominator
def real(x):
    x=Surd.lift(x)
    return rational(x.a)+root2*rational(x.b)
def primitive(a,degree):
    if a==0:return iv.mpf(0)
    x=real(a)
    return x**(degree+1)*(iv.log(x)-iv.mpf(1)/(degree+1))/(degree+1)

A=real(Surd(Q(17,28),Q(-3,14)))
bad=V/2-q*J*J/4
B=real(bad);theta=1-B/A;beta=theta/2-iv.mpf(1)/4
kap=real(q*(2*V-J)/4)
old=real(Surd(Q(39,14),Q(25,42)))
cells=[(l,r,'L') for l,r in zip((Surd(0),R),(R,Surd(half)))]
knots=[half+t for t in (Surd(0),J,F,V,G,R)]
cells += [(l,r,layer) for layer in ('+','-') for l,r in zip(knots,knots[1:])]
alpha=4
coef=iv.mpf(7)/5
logdet,mean,moment=map(iv.mpf,(0,0,0))
for l,r,layer in cells:
    cell=Cell(l,r,layer)
    lo0,hi0=cell.edges(l);lo1,hi1=cell.edges(r)
    dt0,dt1=hi0-lo0,hi1-lo1
    slope=1 if layer=='L' else 2
    k=iv.mpf(slope)/2
    offset={'L':0,'+':-half,'-':half}[layer]
    a0=max(half-l,l-half-V,Surd(0));a1=max(half-r,r-half-V,Surd(0))
    active=(a0+a1)>0
    if active:
        # The area-weighted log(a) singularity is integrated exactly.
        m=(dt1-dt0)/(a1-a0);t=dt0-m*a0
        z0,z1=sorted((a0,a1))
        logdet+=real(t)*(primitive(z1,0)-primitive(z0,0))+real(m)*(primitive(z1,1)-primitive(z0,1))
    ds=real(r-l)/pieces
    s0,slope_s=real(l),real(r-l)
    a0i,dai=real(a0),real(a1-a0)
    widths=real(dt0),real(dt1-dt0)
    d0=real(Surd(Q(3,2))-slope*lo0-offset)
    d1=real(-slope*(lo1-lo0))
    t0=real(Surd(Q(3,2))-slope*hi0-offset)
    t1=real(-slope*(hi1-hi0))
    for j in range(pieces):
        t=iv.mpf([j,j+1])/pieces
        s=s0+t*slope_s;a=a0i+t*dai
        width=widths[0]+widths[1]*t
        dl=d0+t*d1;dh=t0+t*t1
        g0=alpha*s*s-coef*s
        reciproc=iv.log(dl/dh)/slope
        mean+=ds*(width*g0+a**2*reciproc)
        moment+=ds*(width*g0**2+2*g0*a**2*reciproc+a**4*(1/dh-1/dl)/slope)
        if active:
            logD=(dl*(iv.log(dl)-1)-dh*(iv.log(dh)-1))/slope
            logdet+=ds*(width*iv.log(k*iv.sqrt(alpha))-iv.mpf(3)/2*logD)
        else:
            logdet+=ds*width*iv.log(k*alpha)
# Given a physical common step, the exact midpoint has one primary lift.
# Count the opposite angular lift precisely on the overlap of the upper charts.
overlap=Surd(0)
for l,r in zip(knots,knots[1:]):
    def shared(s):
        a,c=Cell(l,r,'+').edges(s)
        b,d=Cell(l,r,'-').edges(s)
        low0,high0=2*a-half,2*c-half
        low1,high1=2*b+half,2*d+half
        assert low0<=low1<=high0<=high1
        return high0-low1
    overlap+=(r-l)*(shared(l)+shared(r))/2
mu=logdet/A+iv.log(8)-real(overlap)/A*iv.log(2)
sigma=iv.sqrt(moment/A-(mean/A)**2)
d=1-theta
c=kap*iv.sqrt(32)/(A*d)
C=iv.exp(mu-d)*c**(-d)*iv.log(1/A)**(-beta)/(4*iv.pi*iv.exp(1)*iv.sqrt(2*iv.pi)*sigma)
ratio=(old/kap)**d
print('mu',mu,'sigma',sigma,'H/m',c,'prefactor',C,'ratio',ratio,sep='\n')
if pieces>=512:
    assert C.a>iv.mpf('0.0141') and ratio.a>iv.mpf('2.85')
