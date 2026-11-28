"""Two exact Bernstein certificates for the improved 39/125 bound."""
from fractions import Fraction as Q
from math import comb

GAP=Q(39,125)-Q(304098,10**6)
EPS=Q(5,16)-Q(39,125)
KNOT=Q(21,400)
P=[Q(153,208),-Q(61,26),Q(24,13)]


def bernstein(p,a,b):
    n=len(p)-1
    power = [sum(p[j]*comb(j,i)*a**(j-i)*(b-a)**i for j in range(i,n+1)) for i in range(n+1)]
    return [sum(power[i]*Q(comb(k,i),comb(n,i)) for i in range(k+1)) for k in range(n+1)]


def polynomial(lam):
    t=1-2*lam
    return [t*GAP/2-EPS*P[0],
            GAP*(1-lam*lam)-EPS*P[1]-t*P[0]/8,
            -EPS*P[2]-t*P[1]/8,-t*P[2]/8]


def intervals():
    for lam,a,b in [(Q(1,4),Q(0),KNOT),(Q(1,2),KNOT,Q(1,2))]:
        p=polynomial(lam)
        while p[-1]==0:
            p.pop()
        yield lam,a,b,p,bernstein(p,a,b)


if __name__=='__main__':
    for lam,a,b,p,coefficients in intervals():
        assert all(x>0 for x in coefficients)
        print('lambda =',lam,'interval',a,b,'Bernstein lower bound',min(coefficients))
