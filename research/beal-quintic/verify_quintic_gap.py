"""Independently replay the modular exclusions for consecutive fifth powers."""
from math import isqrt
from pathlib import Path


def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def prime_divisors(n):
    divisors = []
    d = 2
    while d*d<=n:
        if n%d==0:
            divisors.append(d)
            while n%d==0:
                n//=d
        d+=1
    if n>1:
        divisors.append(n)
    return divisors


def power_residues(p,q):
    """All pth powers in F_q, generated from a primitive root."""
    factors = prime_divisors(q-1)
    g = next(g for g in range(2,q) if all(pow(g,(q-1)//t,q)!=1 for t in factors))
    step = pow(g,p,q)
    h = 1
    values = {0}
    for _ in range((q-1)//p):
        values.add(h)
        h=h*step%q
    assert h==1 and len(values)==1+(q-1)//p
    return values


def main():
    file=Path(__file__).with_name('quintic_gap_witnesses.txt')
    rows=[list(map(int,s.split())) for s in file.read_text().splitlines()]
    exponents=[n for n in range(7,5042) if prime(n)]
    assert [r[0] for r in rows]==exponents
    total=0
    for p,*qs in rows:
        possible=list(range(3,8*p,2))
        total+=len(possible)
        for q in qs:
            assert prime(q) and (q-1)%p==0
            powers=power_residues(p,q)
            targets={16*h%q for h in powers}
            allowed={t for t in powers if (t**4+10*t*t+5)%q in targets}
            possible=[u for u in possible if pow(u,p,q) in allowed]
        if possible:
            raise ArithmeticError(f"survivors for p={p}: {possible}")
    print(f"All {total:,} odd base candidates excluded across {len(rows)} prime exponents.")


if __name__=='__main__':
    main()
