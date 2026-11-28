"""Exact capacity of a two-arc envelope. Python 3, standard library only.

Homogeneous coordinates are two lengths and two gaps, (a,b,g,h).
Enumerate vertices by 3x3 minors after normalizing their sum to one.
"""
from itertools import combinations, combinations_with_replacement, product
from functools import reduce
from math import gcd

def add(p, q):
    return tuple(x+y for x,y in zip(p,q))

def sub(p, q):
    return tuple(x-y for x,y in zip(p,q))

def scale(n, p):
    return tuple(n*x for x in p)

def dot(p, q):
    return sum(x*y for x,y in zip(p,q))

def primitive(v):
    divisor = reduce(gcd, v, 0)
    return tuple(x//divisor for x in v) if divisor else v

def det(u, v, w):
    return (u[0]*(v[1]*w[2]-v[2]*w[1])
            -u[1]*(v[0]*w[2]-v[2]*w[0])
            +u[2]*(v[0]*w[1]-v[1]*w[0]))

def vertex(planes):
    v = []
    for i in range(4):
        minor = [row[:i]+row[i+1:] for row in planes]
        v.append((-1)**i * det(*minor))
    if sum(v) < 0:
        v = [-x for x in v]
    if sum(v) and all(dot(f,v)>=0 for f in domain):
        return primitive(v)
    return None

def vertices(planes):
    return {v for triple in combinations(planes,3) if (v:=vertex(triple))}

a,b,g,h = [tuple(int(j==i) for j in range(4)) for i in range(4)]
period=(1,1,1,1)
zero=(0,0,0,0)
domain=[a,b,g,h,sub(a,b),sub(h,g),sub(period,scale(2,a))]
corners=vertices(domain)
ends=(zero,a,add(a,g),add(add(a,g),b))
sums={add(p,q) for p,q in combinations_with_replacement(ends,2)}
# Twice the best attainable loss is a continuous piecewise-linear selection
# from this list. Include changes of order between every two candidates.
branches=[zero,scale(2,b),sub(add(add(a,b),g),h),sub(a,h),sub(b,g),
          sub(add(a,b),add(g,h))]
def active_planes(forms):
    planes=set(domain)
    for f in forms:
        lo=min(dot(f,v) for v in corners)
        hi=max(dot(f,v) for v in corners)
        if lo<0<hi:
            v=primitive(f)
            planes.add(max(v,scale(-1,v)))
    return sorted(planes)

def target(v):
    A,B,G,H=v
    return min(2*B,max(0,A+B+G-H),max(0,A-H)+max(0,B-G))

def intersection(v, shift):
    A,B,G,H=v
    T=sum(v)
    arcs=((0,A),(A+G,A+G+B))
    return sum(max(0,min(r,shift+k*T-p)-max(l,shift+k*T-d))
               for (l,r),(p,d) in product(arcs,repeat=2) for k in range(-2,3))

def verify():
    order=[sub(p,q) for p,q in combinations(branches,2)]
    total=0
    all_vertices=set()
    for s in sorted(sums):
        hinges=[add(sub(s,t),scale(k,period)) for t in sums for k in range(-2,3)]
        points=vertices(active_planes(order+hinges))
        assert corners<=points
        for v in points:
            val=intersection(v,dot(v,s))
            assert val>=target(v),(v,s,val,target(v))
        total+=len(points)
        all_vertices.update(points)
    print(len(sums),'endpoint-sum traces;',total,'exact vertex comparisons;',
          len(all_vertices),'distinct shapes.')
if __name__=='__main__':
    verify()
