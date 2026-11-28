"""Independent exact tests of guarded products in all remainder widths."""
from collections import Counter
from math import prod

def largest_seed(t):
    n=2**t
    def search(prefix, start):
        yield prefix
        for x in range(start,n):
            if all(2*y-x not in prefix for y in prefix):
                yield from search((*prefix,x),x+1)
    return max(search((),0),key=len)

def information_leq_deficit(points, j, seed, bits):
    rows=Counter(x%(2**j) for x in points)
    columns=Counter(x//(2**j) for x in points)
    n=len(points)
    p=prod(v**v for v in rows.values())*prod(v**v for v in columns.values())
    return (n*len(seed))**n <= 2**(bits*n)*p

seeds=[largest_seed(i) for i in range(5)]
checks=sets=0
for t in range(1,5):
    base=2**(t+1)
    for k in range(1,4):
        whole=[0]
        for i in range(k):whole=[v+base**i*w for v in whole for w in seeds[t]]
        for r in range(t+1):
            a=[v+base**k*w for v in whole for w in (seeds[r-1] if r else (0,))]
            d=k*(t+1)+r
            points=set(a)
            assert len(points)==len(a) and max(a)<2**d
            assert all(2*y-x not in points for x in a for y in a if x<y)
            for j in range(1,d):
                assert information_leq_deficit(points,j,seeds[t],t)
                checks+=1
            sets+=1
print('Guarded products:',sets,'; exact information bounds:',checks,'; seed sizes:',list(map(len,seeds)))
