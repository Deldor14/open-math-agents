"""Exact lower witnesses on [19,57) and an exhaustive upper bound at 19."""
from itertools import combinations
from math import isqrt


def witness(n,size):
    def search(available,chosen):
        if len(chosen)==size:
            return tuple(chosen)
        while bin(available).count("1")>=size-len(chosen):
            bit=available & -available
            x=bit.bit_length()-1
            available ^= bit
            blocked=sum(1 << (2*x-a) for a in chosen)
            result=search(available & ~blocked,chosen+[x])
            if result is not None:
                return result
        return None
    return search((1<<n)-1,[])


def verify():
    # A separate full enumeration at length 19 supplies the upper bound.
    n=19
    nonfree=[(1<<a)|(1<<(a+d))|(1<<(a+2*d)) for d in range(1,10) for a in range(n-2*d)]
    masks=(sum(1<<x for x in c) for c in combinations(range(n),9))
    candidates=sum(1 for mask in masks if all(mask & p != p for p in nonfree))
    assert candidates==0
    print('9-subsets free at length 19:',candidates)
    needed=0
    bounds=[]
    for m in range(19,57):
        k=isqrt((64*m-1)//19)+1
        if k>needed:
            chosen=witness(m,k)
            assert len(chosen)==k
            assert all(2*b!=a+c for a,b,c in combinations(chosen,3))
            bounds.append((m,chosen))
            needed=k
        assert 64*m<=19*needed**2
    for m,chosen in bounds:
        print(m, *chosen)


if __name__=='__main__':
    verify()
