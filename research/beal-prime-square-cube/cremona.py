"""Recover positive coprime square/cube pairs from the pinned Cremona tables."""
from math import gcd, isqrt
from pathlib import Path
import hashlib
import json
import sys
from classify import root

LIMIT = 499999
REVISION = '6fedd3ab463a70e52061ebc0b04832ad19fd2e01'


def conductor_primes():
    sieve = bytearray(b'\x01') * (LIMIT + 1)
    for n in range(2,isqrt(LIMIT)+1):
        if sieve[n]:
            sieve[n*n::n] = bytes(len(sieve[n*n::n]))
    levels = {}
    for p in range(5,LIMIT+1):
        if sieve[p]:
            for a in range(7):
                for b in range(4):
                    N = p * 2**a * 3**b
                    if N <= LIMIT:
                        levels[N] = p
    return levels


def scan(directory,manifest):
    levels = conductor_primes()
    solutions = {}
    nrows = 0
    relevant = 0
    records = [l.split() for l in manifest.read_text().splitlines()]
    blocks = set()
    for name,size,blob in records:
        lo,hi = map(int,name.split('.')[1].split('-'))
        assert hi == lo + 9999 and lo not in blocks
        blocks.add(lo)
        data = (directory/name).read_bytes()
        assert len(data)==int(size)
        assert hashlib.sha1(b'blob '+size.encode()+b'\0'+data).hexdigest()==blob
        for row in data.splitlines():
            nrows += 1
            fields = row.split()
            N = int(fields[0])
            assert lo <= N <= hi
            p = levels.get(N)
            if p is None:
                continue
            relevant += 1
            a1,a2,a3,a4,a6 = map(int,fields[3][1:-1].split(b','))
            b2,b4,b6 = a1*a1+4*a2, a1*a3+2*a4, a3*a3+4*a6
            c4 = b2*b2 - 24*b4
            c6 = -b2**3 + 36*b2*b4 - 216*b6
            if c4 >= 0 or c6 == 0:
                continue
            num,den = -c4**3,c6*c6
            g = gcd(num,den)
            cube,square = num//g,den//g
            total = cube+square
            k = 0
            while total % p == 0:
                k += 1
                total //= p
            if total != 1 or k < 3:
                continue
            u,v = isqrt(square),root(cube,3)
            if u*u == square and v**3 == cube:
                key = (p,k,u,v)
                label = ''.join(f.decode() for f in fields[:3])
                if key not in solutions or N < solutions[key][0]:
                    solutions[key] = (N,label)
    assert blocks == set(range(0,LIMIT+1,10000))
    assert nrows == 3064705
    return {'rows':nrows,'examined_levels_rows':relevant,
            'solutions': [list(s)+list(solutions[s]) for s in sorted(solutions)]}


if __name__ == '__main__':
    print(json.dumps(scan(Path(sys.argv[1]),Path(sys.argv[2])),indent=2))
