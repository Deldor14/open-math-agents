"""Return every candidate exponent for two B-smooth bases."""
from math import isqrt
import sys


def primes_to(n):
    marks = bytearray([1])*(n+1)
    marks[:2] = bytes(2)
    for p in range(2,isqrt(n)+1):
        if marks[p]:
            marks[p*p::p] = bytes((n-p*p)//p+1)
    return [p for p in range(2,n+1) if marks[p]]


def factors(n,primes):
    for p in primes:
        if p*p>n:
            break
        if n%p==0:
            yield p
            while n%p==0:
                n//=p
    if n>1:
        yield n


def possible(limit):
    small = primes_to(limit+2)
    out = set()
    for r in small:
        if r==7 or r>limit:
            continue
        f = next(i for i in [1,2,3,6] if pow(r,i,7)==1)
        polys = {1:r-1,2:r+1,3:r*r+r+1,6:r*r-r+1}
        for d,n in polys.items():
            if f%d==0:
                out.update(factors(n,small))
    return sorted(p for p in out if p>=11)


if __name__=='__main__':
    for p in possible(int(sys.argv[1])):
        print(p)
