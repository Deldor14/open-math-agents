"""Verify reduced cycles and the exact law on different active row sets."""
from collections import Counter
from itertools import product
from math import comb,gcd


def verify(b,T,U,V,n):
    cases=[]
    for q in range(1,n):
        g=gcd(q,b)
        if g>b//2:
            continue
        t=b//g
        for a in range(n-(t-1)*q):
            sites=tuple(range(a,a+t*q,q))
            assert len({x%b for x in sites})==t
            assert {x%b for x in sites}==set(range(a%g,b,g))
            selected=tuple((i,x//b) for x in sites for i,u in enumerate(U) if x%b==u)
            cases.append((selected,Counter()))
    # The acceptance vectors of different tests with the same row/height
    # pairs coincide even when their positions in the progression differ.
    histograms={tuple(sorted(probe)):Counter() for probe,_ in cases}
    for shifts in product(range(2*T),repeat=len(U)):
        for probe,hist in histograms.items():
            count=sum(h+shifts[i]-T in V for i,h in probe)
            hist[count]+=1
    for probe,hist in histograms.items():
        s=len(probe)
        law={j:(2*T)**(len(U)-s)*comb(s,j)*len(V)**j*(2*T-len(V))**(s-j) for j in range(s+1)}
        assert hist==law
    return len(cases),len(histograms)


if __name__=='__main__':
    a=verify(16,3,(0,1,6,7),{0,2},43)
    b=verify(12,3,(0,1,3,4),{0,2},33)
    print('progressions:',a[0]+b[0],'distinct row/height tests:',a[1]+b[1])
