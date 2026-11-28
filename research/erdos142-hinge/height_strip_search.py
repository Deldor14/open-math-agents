"""Exact search for the smallest tilted strip containing an AP-free integer graph."""
from fractions import Fraction as Q
from math import ceil, floor
from itertools import combinations
import sys

def witness(n,width):
    # Normalize by integer vertical translations, integer shears and sign reflection.
    values=[0]
    def extend(lo,hi):
        j=len(values)
        if j==n:return tuple(values)
        for h in range(ceil(j*lo-width),floor(j*hi+width)+1):
            if any(h+values[j-2*d]==2*values[j-d] for d in range(1,j//2+1)):
                continue
            left,right=lo,hi
            for i,v in enumerate(values):
                left=max(left,(h-v-width)/(j-i));right=min(right,(h-v+width)/(j-i))
                if left>right:break
            else:
                values.append(h);sol=extend(left,right)
                if sol is not None:return sol
                values.pop()
        return None
    return extend(Q(0),Q(1,2))

def solve(n,lower=Q(0)):
    ceiling=max(1,ceil(lower))
    while witness(n,Q(ceiling)) is None:ceiling+=1
    candidates=sorted({Q(a,b) for b in range(1,max(n,3)) for a in range(ceil(lower*b),ceiling*b+1)})
    bottom,top=0,len(candidates)-1
    while bottom<top:
        mid=(bottom+top)//2
        if witness(n,candidates[mid]) is None:bottom=mid+1
        else:top=mid
    w=candidates[bottom];v=witness(n,w)
    assert v is not None
    assert all(i+k!=2*j or v[i]+v[k]!=2*v[j] for i,j,k in combinations(range(n),3))
    slopes={Q(0),Q(1,2)}|{Q(v[j]-v[i],j-i)for i,j in combinations(range(n),2)}
    best,sl=min((max(z-i*s for i,z in enumerate(v))-min(z-i*s for i,z in enumerate(v)),s) for s in slopes if 0<=s<=Q(1,2))
    assert best==w
    return w,sl,v

if __name__=='__main__':
    maximum=int(sys.argv[1]) if len(sys.argv)>1 else 16
    lower=Q(0)
    for n in range(2,maximum+1):
        lower,s,vals=solve(n,lower)
        print(n,lower,s,','.join(map(str,vals)),flush=True)
