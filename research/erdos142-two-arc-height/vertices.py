"""Independent 2D vertex certificate for the reflection obstruction on upper rows.

Usage: python vertices.py <directory containing the original polygon modules>
"""
import sys
from fractions import Fraction as Q
from itertools import combinations, combinations_with_replacement, product
sys.path.insert(0,sys.argv[1])
from verifica_parametro import Surd, R, J, F, V, G, q as b

zero=Surd(0)
one=Surd(1)
half=one/2
assert J==2*F-V and F==(3*R-1)/2 and G==R/2
assert zero<J<F<V<G<R<half
# Each line is stored as its intercept and slope in height u.
def val(line,u):return line[0]+line[1]*u
def add(x,y):return x[0]+y[0],x[1]+y[1]
def up(x):return max(zero,x)
r=(zero,b*(1-R))
c_a=(b*R,-b*R)
c_b=(b*(1-R)/2,b*(1-R))
neg_d_a=(-half,b*(1-R))
neg_d_b=(b*R/2-half,-b*R)
neg_l=(b*R-half,-b*R)
assert add(c_a,(-c_b[0],-c_b[1]))==(b*F,-b)
assert add(neg_d_b,(-neg_d_a[0],-neg_d_a[1]))==(b*G,-b)

def edges(u):
    return [val(r,u),min(val(c_a,u),val(c_b,u)),
            max(val(neg_d_a,u),val(neg_d_b,u)),val(neg_l,u)]

def target(u):
    f=b*up(F-u)
    g=b*up(G-u)
    v=b*up(V-u)/2
    return 2*b*(R-u)-g-v-max(f,v)

def difference(u,t):
    e=edges(u)
    assert -half<=e[2]<=e[3]<=0<=e[0]<=e[1]<=half
    signed=list(zip(e,(1,-1,1,-1)))
    # The convolution of two real interval indicators is a sum of four
    # first-power hinges. Periodize at t and t-1; every other lift is zero.
    reflected=sum((i*j*up(t+h-x-y) for h in (-1,0)
        for (x,i),(y,j) in product(signed,repeat=2)),zero)
    return reflected-2*((e[1]-e[0])+(e[3]-e[2])-target(u))

candidates=(r,c_a,c_b,neg_d_a,neg_d_b,neg_l)
lines={(zero,zero),(one,zero)}
for x,y in combinations_with_replacement(candidates,2):
    for n in (0,1):
        intercept,slope=add(x,y)
        lines.add((intercept+n,slope))
# Vertical lines cover the formula changes in the envelope and target.
# Every remaining line is an overinclusive hinge boundary of the convolution.
verticals=(zero,J,F,V,G,R)
vertices=set()
for u in verticals:
    for l in lines:
        t=val(l,u)
        if zero<=t<=one:vertices.add((u,t))
for a,c in combinations(lines,2):
    if a[1]==c[1]:continue
    u=(c[0]-a[0])/(a[1]-c[1])
    if zero<=u<=R:
        t=val(a,u)
        if zero<=t<=one:vertices.add((u,t))
gaps=[difference(u,t) for u,t in vertices]
assert min(gaps)==0
print('Arrangement:',len(lines),'nonvertical lines;',len(verticals),'verticals;',
      len(vertices),'distinct vertices;',sum(d==0 for d in gaps),'sharp vertices.')
print('Minimum of convolution minus required loss: exactly zero.')
