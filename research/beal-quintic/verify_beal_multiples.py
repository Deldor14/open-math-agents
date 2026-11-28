"""Replay the two good-reduction certificates with elementary finite-field arithmetic."""
from json import loads
from math import isqrt
from pathlib import Path


def square_lifts(prime, B, point, scale):
    assert prime > 5 and all(prime % k for k in range(2,isqrt(prime)+1))
    assert 27*B*B % prime != 0
    gx, gy = (t % prime for t in point)
    assert (gy**2-gx**3-B) % prime == 0
    squares = {t*t % prime for t in range(prime)}
    # Test (Y/scale-1) without division: scale*(Y-scale) differs by a square factor.
    flags = [True]
    seen = set()
    x,y = gx,gy
    while (x,y) not in seen:
        assert (y*y-x**3-B) % prime == 0
        seen.add((x,y))
        flags.append(scale*(y-scale) % prime in squares)
        if x == gx and (y+gy) % prime == 0:
            return flags
        if x == gx:
            assert y == gy
            num, den = 3*x*x, 2*y
        else:
            num, den = y-gy, x-gx
        slope = num*pow(den,-1,prime) % prime
        new_x = (slope*slope-x-gx) % prime
        x,y = new_x, (slope*(x-new_x)-y) % prime
    raise ArithmeticError('Point repeated before infinity')


def verify(record, B, P, K, target):
    assert (record['B'],record['point'],record['divisor'],record['target']) == (B,P,K,target)
    period = 1
    keep = [0]
    cache = {}
    for factor, witnesses in record['stages']:
        assert isinstance(factor,int) and factor >= 2
        keep = [period*j+n for j in range(factor) for n in keep]
        period *= factor
        for prime in witnesses:
            if prime not in cache:
                cache[prime] = square_lifts(prime,B,P,K)
            flags = cache[prime]
            assert period % len(flags) == 0
            keep = [n for n in keep if flags[n % len(flags)]]
        assert keep == target
    assert str(period)==record['modulus']
    print(f'Y^2=X^3+{B}: {keep} modulo {period}; {len(cache)} primes, {len(record["stages"])} stages')


if __name__ == '__main__':
    assert __debug__, 'Run with assertions enabled'
    records = loads(Path(__file__).with_name('BealMultiples.json').read_text())
    assert len(records)==2
    verify(records[0],2000,[20,100],50,[0,1])
    verify(records[1],80,[4,12],10,[0])
