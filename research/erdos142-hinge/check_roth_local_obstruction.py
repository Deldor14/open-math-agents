"""Direct enumeration of single-window obstructions and the special residue classes."""
from itertools import combinations
from math import gcd
from check_roth_pinned_windows import exact_thresholds, families


def all_windows(n):
    for q in range(1,n):
        for a in range(n-q):
            entries = 1 << a
            for j, x in enumerate(range(a+q,n,q),2):
                entries |= 1 << x
                yield j,a,q,entries


def verify(n):
    table = list(all_windows(n))
    infinity = n+1
    least = [infinity]*(n+1)
    tested = 0
    for mask in families(n):
        vertices = [x for x in range(n) if mask >> x & 1]
        size = len(vertices)
        completions = 0
        for x,y in combinations(vertices,2):
            sites = [2*x-y,2*y-x]
            if (x+y)%2 == 0:
                sites.append((x+y)//2)
            for z in sites:
                if 0<=z<n:
                    completions |= 1 << z
        for length,a,q,w in table:
            if w & mask:
                continue
            covered = bin(completions & w).count('1')
            assert 4*covered <= 3*size**2
            if gcd(q,3)==1:
                assert 2*covered <= size*(size-1)
            else:
                u = sum((x-a)%q == q//3 for x in vertices)
                v = sum((x-a)%q == 2*q//3 for x in vertices)
                assert 2*covered <= size*(size-1)-u*(u-1)-v*(v-1)+4*u*v
            if covered==length:
                least[length] = min(least[length],size)
            tested += 1
    thresholds = exact_thresholds(n)
    global_min = [s+1 for s in thresholds]
    assert all(x<=y for x,y in zip(global_min,least[2:]))
    return tested, [(i,x,y) for i,(x,y) in enumerate(zip(global_min,least[2:]),2)
                    if x < y and y < infinity]


def digital():
    digits = {0}
    for m in range(8):
        p = 4**m
        u = p-1
        left = [3*(u-x)+1 for x in digits]
        right = [3*u+2+3*y for y in digits]
        seed = set(left+right)
        assert len(seed)==2*2**m and min(seed)>=0 and max(seed)<6*p
        assert all(2*y-x not in seed for x,y in combinations(sorted(seed),2))
        endpoints = {2*y-x for x in left for y in right} | {2*x-y for x in left for y in right}
        assert endpoints == set(range(0,6*p,3))
        digits = {4*x+b for x in digits for b in (0,1)}
    return len(seed),2*p


if __name__=='__main__':
    for n in (9,13,16):
        print('n, disjoint window checks, finite strict gaps (L,global,local):',n,verify(n))
    print('largest example (prescribed sites, length of blocked AP):',digital())
