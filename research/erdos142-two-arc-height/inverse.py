"""Exact constants in the equality and inverse theorems. Pass the original polygon directory."""
import sys
from fractions import Fraction as Q
sys.path.insert(0,sys.argv[1])
from verifica_parametro import Surd, R, J, V, G, q, half
A=Surd(Q(17,28),Q(-3,14))
C=4*A-1
eps=Q(1,10**6)
rho=Q(1,1000)
gain=A-Q(1,4)
short=(1-Surd(0,half))/2
cut=Q(369,1000)
H=(half-cut)/(2*cut)
for ceiling in (Q(1,32),short/3,short*cut,cut*H*(1-H),Q(178483,4194304)):
    assert ceiling<gain-eps
def fan(L):
    g=(C+16*L-4)/14
    return g-C/2,g/2+C/4,g,2*L-half
for L in (Surd(Q(1,3)),Surd(half)):
    j,w,g,T=fan(L)
    assert 0<j and w<=100*j
assert 2*(gain-201*eps)>Q(2,5)*half*half
assert Q(14,9)/Q(2,5)<4
assert Q(41,100)<R-2*rho and R+2*rho<Q(43,100)
for L in (Surd(Q(41,100)),Surd(Q(43,100))):
    j,w,g,T=fan(L)
    assert 0<=j-rho and j+rho<=w<=g-rho and g+rho<=L
    assert j+rho<=T-g-rho and T<=L
    assert w<=2*j and L-w<=2*(L-g)
    assert 1-2*L+j+g>=Q(9,20)
    assert L-g<=Q(23,100)
assert q<Q(11,10)
assert (Q(9,2)+Q(4,7)*q)/Q(9,20)<12
assert Q(7,2)+2*12*Q(23,100)+Q(4,7)*q<10
m,n=q*(1-R),q*R
assert m>n>0 and m+n==q
assert n==2*q*(R-G) and q*(1-2*R+J+G)==half
assert R*2-half>G and q*(R-(2*R-half))<n/2
assert half-n*R<R and half-m*R<R
print('Strict gap filters, both length ranges and the 12/10/22 slope constants checked exactly.')
print('Equality switches recover the two optimal slopes and full terminal rows.')
