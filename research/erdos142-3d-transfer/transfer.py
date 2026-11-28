"""Derandomize a three-dimensional shell using different small prime grids.

All finite objectives are integral or rational. The asymptotic parameter choice
is large. check.py runs the same two selection steps on small finite grids.
"""
from fractions import Fraction as F
from itertools import product
from math import isqrt, prod


def ceil_root(n, degree):
    lo, hi = 0, 1 << ((n.bit_length()+degree-1)//degree)
    while hi-lo > 1:
        mid = (lo+hi)//2
        if mid**degree >= n:
            hi = mid
        else:
            lo = mid
    return hi


def primes_in_window(start):
    end = 2*start
    prime = bytearray([1])*(end+1)
    for p in range(2,isqrt(end)+1):
        if prime[p]:
            prime[p*p::p] = bytes((end-p*p)//p+1)
    return [p for p in range(max(3,start),end+1) if prime[p]]


def choose_axis(weights, primes, scale, a):
    # Only a multiple of p fails to permute the prime residues. A dyadic
    # window costs at most sum_p N/p = O(N) visits to weight entries.
    p = min(primes,key=lambda q: sum(weights[q-1::q]))
    buckets = [0]*p
    for d,value in enumerate(weights,1):
        buckets[d%p] += value
    top = a.denominator*p*p
    values = []
    for j in range(p):
        bottom = top + a.numerator*min(j,p-j)**2
        values.append((scale*top+bottom-1)//bottom)
    def objective(slope):
        return sum(v*values[d*slope%p] for d,v in enumerate(buckets))
    h = min(range(p),key=objective)
    new = [v*values[(d*h)%p] for d,v in enumerate(weights,1)]
    return (p,h),new


def directions(N,m,T):
    B = ceil_root(N,3*m)
    size = max(3, 32*B*(T+1)*(N.bit_length()+1)**2)
    while True:
        ps = primes_in_window(size)
        weights = [1]*(N-1)
        axes = []
        for c in (F(1024*B*B*T),F(1024*B*B),F(1024*B*B,T))*m:
            axis,new = choose_axis(weights,ps,size,c)
            if c*sum(new)**2 > (8*size*sum(weights))**2:
                break
            axes.append(axis)
            weights = new
        else:
            assert sum(weights)*4**m < size**(3*m)
            return [axes[3*i:3*i+3] for i in range(m)]
        size *= 2


def residue(i,axes):
    # Directions are for (z, 2s, 2t); energy is evaluated on (z,s,t).
    return tuple(i*h*(pow(2,-1,p) if axis else 1)%p
                 for axis,(p,h) in enumerate(axes))


def add_phase(point,shift,primes):
    return tuple((u+v)%p for u,v,p in zip(point,shift,primes))


def grid_data(axes,energy):
    primes = tuple(p for p,h in axes)
    table = {}
    for u in product(*(range(p) for p in primes)):
        point = tuple(F(j,p) for j,p in zip(u,primes))
        value = energy(*point)
        if value is not None:
            table[u] = value
    if not table:
        return None
    mean = F(sum(table.values()),len(table))
    centered = {u:v-mean for u,v in table.items()}
    variance = F(sum(t*t for t in centered.values()),len(table))
    return primes,centered,variance


def bucket_moments(alive,axes):
    stats = {}
    for i,x in alive.items():
        b = stats.setdefault(residue(i,axes),[0,0,0])
        b[0] += 1
        b[1] += x
        b[2] += x*x
    return stats


def pick_shift(alive,axes,grid,constant):
    primes,table,_ = grid
    stats = bucket_moments(alive,axes)
    def objective(shift):
        total = 0
        for u,(count,first,second) in stats.items():
            t = table.get(add_phase(u,shift,primes))
            if t is not None:
                total += (constant-t*t)*count-2*t*first-second
        return total
    best = max(product(*(range(p) for p in primes)),key=objective)
    survivors = {}
    for i,c in alive.items():
        t = table.get(add_phase(residue(i,axes),best,primes))
        if t is not None:
            survivors[i] = c+t
    return best,survivors


def translate(N,vectors,energy):
    grids = [grid_data(axes,energy) for axes in vectors]
    if any(g is None for g in grids):
        return {},[],0
    remaining = sum(g[2] for g in grids)
    limit = 4*remaining+1
    alive = {i:0 for i in range(1,N+1)}
    shifts = []
    for axes,grid in zip(vectors,grids):
        remaining -= grid[2]
        h,alive = pick_shift(alive,axes,grid,limit-remaining)
        shifts.append(h)
    density = prod(F(len(grid[1]),prod(grid[0])) for grid in grids)
    assert sum(limit-x*x for x in alive.values()) >= F(3,4)*limit*N*density
    return alive,shifts,limit


def min_metric(N,vectors,T):
    def value(d):
        s = F(0)
        for axes in vectors:
            for (p,h),c in zip(axes,(T*T,T,1)):
                a = d*h%p
                s += c*F(min(a,p-a)**2,p*p)
        return s
    return min(map(value,range(1,N)))


def window(alive,minimum):
    if minimum <= 0 or not alive:
        return [1]
    points = sorted((v,i) for i,v in alive.items())
    left = start = end = 0
    for right,(v,i) in enumerate(points):
        while 16*(v-points[left][0]) >= minimum:
            left += 1
        if right+1-left > end-start:
            start,end = left,right+1
    return sorted(i for v,i in points[start:end])


def dimension(N,rho):
    # The squared comparison incorporates m^(-1/2) and the sixth root term.
    # Restrict to a constant-factor neighborhood of sqrt(log N) so all the
    # optional parameter comparisons and the chosen execution obey the bound.
    L=N.bit_length()
    root=isqrt(L)
    def score(m):
        return rho**(2*m)/(m*ceil_root(N,3*m)**4)
    return max(range(max(1,root//4),2*root+3),key=score)


def construct(N,block):
    if N < 1:
        raise ValueError('positive interval length required')
    if N == 1:
        return [1]
    m = dimension(N,block.volume)
    T = 32*max(4*block.k,2*block.n)*m
    vectors = directions(N,m,T)
    alive,_,_ = translate(N,vectors,lambda z,s,t:block.energy(z,s,t,T))
    minimum = min_metric(N,vectors,T)
    assert 1024*ceil_root(N,3*m)**2*minimum > m*T
    return window(alive,minimum)
