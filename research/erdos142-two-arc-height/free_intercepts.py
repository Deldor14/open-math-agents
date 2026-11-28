"""Exact one-dimensional certificate for charging arbitrary upper rows across the flat family."""
import sys
from fractions import Fraction as Q
sys.path.insert(0,sys.argv[1])
from verifica_parametro import Surd, q as speed, R, V, J, G, half
zero=Surd(0)
quarter=Q(1,4)
alpha=speed*(1-R)/2
beta=speed*R/2
t=alpha+beta
Z0=speed*R
zJ=Z0-speed*J
zV=Z0-speed*V
edge=beta+t/2
assert speed==2*t and beta/speed==G
assert zero<zV-beta<zJ-t/2<beta<zV<alpha<zJ<Z0<edge<half
assert half-t/2<zV and Z0<half<t
assert V+2*G-half>0 and 2*G<half
assert Z0==(half+2*alpha+beta)/3 and alpha>=beta
assert Z0==half-(5-Surd(0,3))/14

def pos(x):
    return max(zero,x)

def lines(z,k=0):
    X,Y=min(z,alpha)+k,min(z,beta)
    return [X+Y-z,quarter+X+Y/2-3*z/2,half-z]

def W(z,k=0):
    return z+pos(min(lines(z,k)))

def extra(z):
    return 2*pos(z-t/2-beta) if z>=zJ else zero

def verify():
    nodes=sorted({zero,beta,zV,alpha,zJ,Z0,edge,Surd(half)})
    crossings=set(nodes)
    for lo,hi in zip(nodes,nodes[1:]):
        for f in (lambda z:lines(z),lambda z:lines(z,extra(z))):
            a=[zero]+f(lo)
            b=[zero]+f(hi)
            for i in range(len(a)):
                for j in range(i):
                    u,v=a[i]-a[j],b[i]-b[j]
                    if u*v<0:crossings.add(lo+(hi-lo)*u/(u-v))
    for z in sorted(crossings):
        k=extra(z)
        assert k<=pos(z-alpha) and W(z,k)==W(z)
        if z<=beta:assert W(z)==2*z
        if beta<=z<=zV:assert W(z)==z+beta
        if zV<=z<=zJ:assert W(z)==half
        if Z0<=z:assert W(z)==z
        if zJ<=z:
            w=z-t/2
            assert pos(z-alpha)+pos(z-beta)==2*w
            assert k==2*pos(w-beta)
            assert 0<w<zV
        if beta<=z<=zV:
            w=z-beta
            assert 0<=w<beta
            assert pos(z-alpha)==0 and pos(z-beta)==w
    print(len(crossings),'exact z knots: plateau, two target bands, enlarged cap and equal capacity.')
if __name__=='__main__':
    verify()
