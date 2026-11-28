"""Deterministically find and check simultaneous counts by conditional expectation."""
from functools import lru_cache
from itertools import product
from math import comb,gcd


def example():
    p,T=256,6
    n=p*T
    U=sorted(sum(a*3**i for i,a in enumerate(digits)) for digits in product((0,1),repeat=5))
    V={0,1,3,4}
    low,high=3,21
    tests=[(a,q) for q in range(1,(n-1)//(p-1)+1) if gcd(q,p)==1 for a in range(n-(p-1)*q)]
    inverses={q:pow(q,-1,p) for _,q in tests}

    @lru_cache(None)
    def bad_ways(r,current):
        return sum(comb(r,j)*len(V)**j*(2*T-len(V))**(r-j) for j in range(r+1)
                   if not low<=current+j<=high)

    potential=len(tests)*bad_ways(len(U),0)
    assert potential<(2*T)**len(U)
    counts=[0]*len(tests)
    shifts=[]
    for index,u in enumerate(U):
        remaining=len(U)-1-index
        heights=[(a+q*((u-a)*inverses[q]%p))//p for a,q in tests]
        def score(s):
            return sum(bad_ways(remaining,count+(h+s-T in V)) for h,count in zip(heights,counts))
        scores=list(map(score,range(2*T)))
        assert sum(scores)==potential
        shift=min(range(2*T),key=scores.__getitem__)
        potential=scores[shift]
        assert potential<(2*T)**remaining
        shifts.append(shift)
        counts=[c+(h+shift-T in V) for h,c in zip(heights,counts)]
    A={u+p*h for u,s in zip(U,shifts) for h in range(T) if h+s-T in V}
    assert all(2*y-x not in A for x in A for y in A if x<y)
    direct=[sum(a+q*i in A for i in range(p)) for a,q in tests]
    assert direct==counts and all(low<=c<=high for c in direct)
    print(f'n={n}, {len(A)} points, {len(tests)} progressions, observed range [{min(counts)},{max(counts)}]')
    print('shifts in increasing tag order:',','.join(map(str,shifts)))


if __name__=='__main__':
    example()
