"""Check the two finite-logarithm identities at every non-axis projective class.

Uses exact integer convolution via Kronecker substitution and the geometric
progression of powers of a generator of F_p^*. No cyclotomic-ring arithmetic.
"""
from math import isqrt
import sys


def primes(limit):
    sieve = bytearray(b'\x01') * (limit+1)
    for d in range(2, isqrt(limit)+1):
        if sieve[d]:
            sieve[d*d::d] = bytes((limit-d*d)//d+1)
    return [v for v in range(11,limit+1) if sieve[v]]


def generator(p):
    n = p-1
    divisors = []
    d = 2
    while d*d<=n:
        if n%d == 0:
            divisors.append(d)
            while n%d==0:
                n//=d
        d+=1
    if n>1:
        divisors.append(n)
    return next(g for g in range(2,p) if all(pow(g,(p-1)//d,p)!=1 for d in divisors))


def integer_coefficients(values, width):
    return int.from_bytes(b''.join(v.to_bytes(width,'little') for v in values),'little')


def all_classes(p):
    m = p-1
    g = generator(p)
    points = [1]
    for _ in range(1,m):
        points.append(points[-1]*g%p)
    # The factors are g^(k choose 2), and their inverses for k<m.
    chirp = [points[(k*(k-1)//2)%m] for k in range(2*m-1)]
    unchirp = [points[-(k*(k-1)//2)%m] for k in range(m)]
    width = ((m**3).bit_length()+7)//8
    kernel = integer_coefficients(chirp,width)
    inverse = [0,1]
    for j in range(2,p):
        inverse.append(p-(p//j)*inverse[p%j]%p)
    indices = [i for i,x in enumerate(points) if pow(x,7,p)!=p-1]
    for l in range(1,4):
        if p%7 in (l,7-l):
            continue
        data = [0]*m
        for j in range(1,p):
            if j%7 not in (l,7-l):
                continue
            sign = 1 if (j%2==1)==(j%7==l) else -1
            k = j%m
            data[m-1-k] = sign*inverse[j]*unchirp[k]%p
        full = (kernel*integer_coefficients(data,width)).to_bytes(width*(3*m-2),'little')
        values = [unchirp[i]*int.from_bytes(full[(m-1+i)*width:(m+i)*width],'little')%p for i in range(m)]
        indices = [i for i in indices if (points[i]**2*values[-i]-values[i])%p==0]
    return [points[i] for i in indices]


if __name__=='__main__':
    upper=int(sys.argv[1])
    lower=int(sys.argv[2]) if len(sys.argv)>2 else 11
    for p in primes(upper):
        if p>=lower:
            print(p,*all_classes(p),flush=True)
