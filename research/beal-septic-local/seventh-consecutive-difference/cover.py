"""A finite cover of the remaining exponent progressions by rational primes."""
from fractions import Fraction
from math import gcd, isqrt, factorial
from pathlib import Path
import sys

here = Path(__file__).resolve().parent
W = 5040
bound = 300000000
rows = [tuple(map(int, s.split())) for s in (here/"classes.txt").read_text().splitlines()]
assert rows == sorted(set(rows)) and len(rows) == 128
assert len({(d,v) for d,v,_ in rows}) == 97
assert all(Fraction(v, v-d**6) < 9 for d,v,_ in rows)
# Upper endpoint in e*log(v/d^6) < (354*(3*log(e)+6.1)^2+2)*log(v).
assert sum(Fraction(20**k, factorial(k)) for k in range(81)) > bound
assert sum(Fraction(21**k, factorial(k)) for k in range(81)) > 10**9
assert 189*(354*(3*20+Fraction(61,10))**2+2) < bound

primes = [q for q in range(5,4000) if all(q%d for d in range(2,isqrt(q)+1))
          and W%(q-1)]
images = {q:{(pow(a+1,7,q)-pow(a,7,q))%q for a in range(q)} for q in primes}


def cover(d,v,r):
    count = (bound-1-r)//W+1
    mask = (1<<count)-1
    if r == 1:
        mask -= 1
    witnesses = []
    for q in primes:
        if d%q == 0:
            continue
        b = v*pow(d,-6,q)%q
        period = (q-1)//gcd(q-1,W) if b else 1
        value, step = pow(b,r,q), pow(b,W,q)
        pattern = 0
        for k in range(period):
            if value in images[q]:
                pattern |= 1<<k
            value = value*step%q
        width = period
        while width < count:
            pattern |= pattern<<width
            width *= 2
        reduced = mask & pattern
        if reduced != mask:
            witnesses.append(q)
            mask = reduced
        if mask == 0:
            return witnesses
    raise ValueError((d,v,r,mask.bit_length()))


if __name__ == "__main__":
    for d,v,r in rows:
        print(d,v,r,*cover(d,v,r))
