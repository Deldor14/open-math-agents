"""Directed enclosures for the calibrated two-perspective Roth prefactor."""
import sys
from fractions import Fraction as Q
from mpmath import iv
sys.path.insert(0,sys.argv[1])
from verifica_parametro import Surd, Cell, half, R, V, J, F, G, q as b
iv.dps=40
n=int(sys.argv[2]) if len(sys.argv)>2 else 1024
zero=Surd(0)
rho_s=Surd(Q(17,28),Q(-3,14))
area_bad=V/2-b*J*J/4
gamma=Q(1,100)
lam_low,lam_up=Q(5,8),Q(5,2)
g_low,g_up=Q(6),Q(7,8)
drift=Q(-17,50)
assert gamma/2-drift-Q(55,100)*lam_low==Q(1,800)
assert 2*b*G<half
def rat(x):return iv.mpf(x.numerator)/x.denominator
def real(x):
    x=Surd.lift(x)
    return rat(x.a)+iv.sqrt(2)*rat(x.b)
def log_primitive(x,k):
    if x==0:return iv.mpf(0)
    val=real(x)
    return val**(k+1)*(iv.log(val)-iv.mpf(1)/(k+1))/(k+1)
def lin(x,y,t):
    return real(x)+t*real(y-x)
def denom(v,g):return 1-g*v**2
def f1(v,g,root):
    return iv.log((1+root*v)/(1-root*v))/(2*root)
def f2(v,g,root):
    return (v/denom(v,g)+f1(v,g,root))/2
def flog(v,g,root):
    return v*iv.log(denom(v,g))-2*v+2*f1(v,g,root)
def flogpos(v,B,C):
    return v*iv.log(B+C*v**2)-2*v+2*iv.sqrt(B/C)*iv.atan2(v*iv.sqrt(C/B),1)
knots=[half+t for t in (zero,J,F,V,G,R)]
cells=[(x,y,'L') for x,y in zip((zero,R),(R,Surd(half)))]
cells.extend((x,y,t) for t in ('+','-') for x,y in zip(knots,knots[1:]))
A=real(rho_s);rho=real(area_bad)/A;beta=iv.mpf(1)/4-rho/2
GAM=rat(gamma)
M1=M2=LOG=iv.mpf(0)
for x,y,t in cells:
    low=t=='L'
    p=1 if low else 2
    off={'L':0,'+':-half,'-':half}[t]
    g=rat(g_low if low else g_up)
    lam=rat(lam_low if low else lam_up)
    shift=Q(1,32) if low else -half
    a0,a1=[max(half-s,s-half-V,zero) for s in (x,y)]
    active=a0>0 or a1>0
    cell=Cell(x,y,t)
    lo0,hi0=cell.edges(x);lo1,hi1=cell.edges(y)
    w0,w1=hi0-lo0,hi1-lo1
    for s0,lo,hi in [(x,lo0,hi0),(y,lo1,hi1)]:
        for edge in (lo,hi):
            vv=p*edge+off-shift
            D=1-(g_low if low else g_up)*vv*vv
            assert half<=D<=1
            if low:assert 2*(half-s0)*(half-s0)<=Q(55,100)*D
            else:assert vv>=0
    if active:
        m=(w1-w0)/(a1-a0);inter=w0-m*a0
        a,big=sorted((a0,a1))
        LOG+=real(inter)*(log_primitive(big,0)-log_primitive(a,0))+real(m)*(log_primitive(big,1)-log_primitive(a,1))
    ds=real(y-x)/n;root=iv.sqrt(g)
    slo,slstep=real(x),real(y-x)
    vlo,vstep=real(p*lo0+off-shift),real(p*(lo1-lo0))
    vhi,vhstep=real(p*hi0+off-shift),real(p*(hi1-hi0))
    wlo,wstep=real(w0),real(w1-w0)
    aa,da=real(a0),real(a1-a0)
    for i in range(n):
        z=iv.mpf([i,i+1])/n
        s=slo+slstep*z;w=wlo+wstep*z
        vl,vh=vlo+vstep*z,vhi+vhstep*z
        a=aa+da*z
        if low: bend=0
        elif x>=half+V:bend=2*real(V)*(s-rat(half))-real(V)**2
        else:bend=(s-rat(half))**2
        phi=GAM*s**2+(1-GAM)*bend-rat(drift)*s
        if active:
            aa2=lam*a**2
            I=(f1(vh,g,root)-f1(vl,g,root))/p
            II=(f2(vh,g,root)-f2(vl,g,root))/p
            M1+=ds*(phi*w+aa2*I)
            M2+=ds*(phi**2*w+2*phi*aa2*I+aa2**2*II)
            LD=(flog(vh,g,root)-flog(vl,g,root))/p
            Bp,Cp=lam+GAM,3*GAM*g
            LP=(flogpos(vh,Bp,Cp)-flogpos(vl,Bp,Cp))/p
            LOG+=ds*(w*iv.log(lam*g)/2+LP/2-3*LD/2)
        else:
            M1+=ds*phi*w
            M2+=ds*phi**2*w
# The physical lifting multiplier is 4 on lower or doubly covered upper points;
# it is 8 on upper points with a single eligible lift.
upper=overlap=zero
for x,y in zip(knots,knots[1:]):
    def lengths(s):
        l,r=Cell(x,y,'+').edges(s)
        m,n_=Cell(x,y,'-').edges(s)
        assert 2*l-half<=2*m+half<=2*r-half<=2*n_+half
        return (r-l+n_-m,2*r-half-(2*m+half))
    w0,h0=lengths(x);w1,h1=lengths(y)
    upper+=(y-x)*(w0+w1)/2;overlap+=(y-x)*(h0+h1)/2
mu=LOG/A+iv.log(4)+real(upper-overlap)/A*iv.log(2)
sigma=iv.sqrt(M2/A-(M1/A)**2)
# At a positive angular carry the limiting negative angular defect is
# at most 2 g(1-g), g=b(G-u). Integrate its square-root trim threshold.
kappa=iv.mpf(0)
for l,r in ((zero,V),(J,V)):
    step=real(r-l)/n
    for i in range(n):
        u=real(l)+step*iv.mpf([i,i+1])
        g=real(b)*(real(G)-u)
        kappa+=real(b)*step*iv.sqrt(g*(1-g))/2
c=kappa/(A*rho)
C=iv.exp(mu-rho)*c**(-rho)*iv.log(1/A)**(-beta)/(4*iv.pi*iv.exp(1)*iv.sqrt(2*iv.pi)*sigma)
print('kappa',kappa,'mu',mu,'sigma',sigma,'H/m',c,'C',C,sep='\n')
if n>=1024:assert C.a>iv.mpf('0.153')
