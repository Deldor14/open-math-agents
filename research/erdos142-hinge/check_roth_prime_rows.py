"""Exact distribution, simultaneous construction and small restricted Ramsey examples."""
from collections import Counter
from itertools import product
from math import comb,gcd


def progressions(n,length):
    for q in range(1,(n-1)//(length-1)+1):
        for a in range(n-(length-1)*q):
            yield a,q,tuple(range(a,a+length*q,q))


def rows(U,V,T,p,n,shifts):
    return {x for x in range(n) if x%p in U and x//p+shifts[U.index(x%p)]-T in V}


def exact_law():
    arrays=tests=0
    for k,p,T,U,V in [(3,5,3,(0,2),(0,2)),(3,7,4,(0,1,3),(0,1,3)),(4,7,4,(0,1,2),(0,1,2)),(4,8,4,(0,1,2),(0,1,2)),(3,6,3,(0,2),(0,1))]:
        n=p*T-1
        red=[frozenset(xs) for _,_,xs in progressions(n,k)]
        blue=[frozenset(xs) for _,q,xs in progressions(n,p) if gcd(q,p)==1]
        histogram=[Counter() for _ in blue]
        for shifts in product(range(2*T),repeat=len(U)):
            A=rows(U,V,T,p,n,shifts)
            assert not any(s<=A for s in red)
            for c,s in zip(histogram,blue):
                c[len(A&s)]+=1
            arrays+=1
        law={j:comb(len(U),j)*len(V)**j*(2*T-len(V))**(len(U)-j) for j in range(len(U)+1)}
        assert all(c==law for c in histogram)
        tests+=len(blue)
    print(f'{arrays} arrays, {tests} exact binomial histograms')


def solve(n,k,p):
    rules=[(sum(1<<x for x in xs),0) for a,q,xs in progressions(n,k)]
    rules.extend((sum(1<<x for x in xs),1) for a,q,xs in progressions(n,p) if gcd(q,p)==1)
    nodes=0

    def search(blue,red):
        nonlocal nodes
        nodes+=1
        while True:
            force=[0,0]
            remaining=[]
            for mask,need in rules:
                opposite=(red,blue)[need]
                if mask&opposite:
                    continue
                unknown=mask&~(red|blue)
                if not unknown:
                    return None
                if unknown&(unknown-1)==0:
                    force[need] |= unknown
                else:
                    remaining.append((unknown,need))
            if force[0]&force[1]:
                return None
            if not any(force):
                break
            red |= force[0]
            blue |= force[1]
        if not remaining:
            return blue
        size=min(bin(mask).count('1') for mask,_ in remaining)
        scores=Counter()
        for mask,_ in remaining:
            if bin(mask).count('1')==size:
                while mask:
                    bit=mask&-mask
                    scores[bit]+=1
                    mask^=bit
        bit=max(scores,key=scores.get)
        found=search(blue|bit,red)
        return found if found is not None else search(blue,red|bit)

    mask=search(0,0)
    A=None if mask is None else {i for i in range(n) if mask>>i&1}
    if A is not None:
        assert not any(set(xs)<=A for _,_,xs in progressions(n,k))
        assert all(set(xs)&A for _,q,xs in progressions(n,p) if gcd(q,p)==1)
    return A,nodes


def thresholds():
    for p,first in [(2,4),(3,8),(5,20),(7,45)]:
        n=first
        last,_=solve(n-1,3,p)
        assert last is not None
        while n<=80:
            A,nodes=solve(n,3,p)
            if A is None:
                print(f'first impossible n for k=3,p={p}: {n}, search nodes {nodes}, preceding witness {tuple(sorted(last))}')
                break
            last=A
            n+=1
        else:
            raise AssertionError('threshold outside test interval')


if __name__=='__main__':
    exact_law()
    thresholds()
