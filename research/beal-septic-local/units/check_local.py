"""Check prime coverage and independently close the extra slopes with x^7=-1.

For the complementary slopes the sibling relative/ computation supplies the
second check. The printed certificates use exponentiation modulo Phi_7.
"""
from math import isqrt
from pathlib import Path
import sys
from units import power, multiply


def main():
    root=Path(__file__).resolve().parent
    bound=int(sys.argv[1]) if len(sys.argv)>1 else 20000
    primes=[p for p in range(11,bound+1) if all(p%d for d in range(2,isqrt(p)+1))]
    rows=[list(map(int,s.split())) for s in (root/'pure.txt').read_text().splitlines()]
    assert rows==[[p,p-2,0,0] for p in primes]
    unitrows=[list(map(int,s.split())) for s in (root/'units.txt').read_text().splitlines()]
    assert [r[0] for r in unitrows]==primes
    assert [r[0] for r in unitrows if r[3]==0 or r[6]==0]==[p for p in (61,5419,12703) if p<=bound]
    special=0
    for p in primes:
        m=p*p
        # At t=-1, E^((p^f)-1) != 1 modulo p^2.
        f=next(i for i in range(1,7) if pow(p,i,7)==1)
        E=[(v*pow(7,-1,m))%m for v in power([-1,1,0,0,0,0],6,m)]
        assert power(E,p**f-1,m)!=[1,0,0,0,0,0]
        special+=1
        if p%7!=1:
            continue
        z=next(r for a in range(2,p) if (r:=pow(a,(p-1)//7,p))!=1)
        # In the split ring evaluate L=(t+Z)/(t+1) at Teichmueller lifts
        # of the six seventh roots. Its p-th power is itself mod p^2,
        # also for integral nonunits. Differentiate only the linear factor.
        roots=[pow(pow(z,j,p),p,m) for j in range(1,7)]
        assert all(pow(r,7,m)==1 for r in roots)
        for x in [(-r)%p for r in roots]:
            lifts=set()
            for r in roots:
                u=(x+r)*pow(x+1,-1,m)%m
                delta=(pow(u,p,m)-u)%m
                assert delta%p==0
                slope=(1-r)*pow(x+1,-2,p)%p
                lifts.add(delta//p*pow(slope,-1,p)%p)
            assert len(lifts)>1
            special+=1
    print(len(primes),'primes;',sum(r[1] for r in rows),'ordinary classes;',special,'singular-output slopes checked independently')


if __name__=='__main__':
    main()
