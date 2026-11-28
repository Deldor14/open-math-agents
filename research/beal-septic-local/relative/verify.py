"""Verify both local tables and the two remaining elliptic trace comparisons."""
from math import isqrt
from pathlib import Path
import sys


def rows(path):
    return [list(map(int,line.split())) for line in Path(path).read_text().splitlines()]


def trace(p, coefficients):
    c2,c4,c6=coefficients
    total=0
    for x in range(p):
        y=(((x+c2)*x+c4)*x+c6)%p
        symbol=pow(y,(p-1)//2,p)
        total-= (-1 if symbol==p-1 else symbol)
    return total


def main():
    bound=int(sys.argv[1])
    ring,log=rows(sys.argv[2]),rows(sys.argv[3])
    primes=[p for p in range(11,bound+1) if all(p%d for d in range(2,isqrt(p)+1))]
    assert [r[0] for r in ring]==primes and [r[0] for r in log]==primes
    assert all(r==[p,1] for p,r in zip(primes,log))
    count=0
    exceptions=[]
    for p,n,relative,norm,final in ring:
        assert n==p-1-(7 if p%7==1 else 1)
        assert relative==1 and final==0
        wieferich=pow(2,p-1,p*p)==1
        assert norm==int(wieferich)
        if wieferich:
            t0=trace(p,(-1,-2,1))
            t1=trace(p,(0,-7,-7))
            assert (t0-t1)%p
            exceptions.append((p,t0,t1))
        count+=n
    print('primes:',len(primes))
    print('non-axis unit classes examined:',count)
    print('base-two exceptions and traces (reference, slope 1):',exceptions)
    print('surviving non-axis classes:',0)

if __name__=='__main__':
    main()
