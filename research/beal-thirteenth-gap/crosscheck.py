"""Independent interval and modular checks. Run with Python 3 and assertions."""
from decimal import Decimal, localcontext
from fractions import Fraction
from functools import lru_cache
from math import gcd, isqrt

GAP = 1000
B = 1 << 832
EXTRA = 1 << 64


def prime(p):
    return p >= 2 and all(p % j for j in range(2, isqrt(p)+1))


def floor_root(n, p):
    guess = 1 << ((n.bit_length()+p-1)//p)
    while True:
        nxt = ((p-1)*guess + n//guess**(p-1))//p
        if nxt >= guess:
            return guess
        guess = nxt


def check_equation(t, h, p):
    if t <= h or (t-h) % 2:
        return
    a = (t-h)//2
    if gcd(a,h) != 1:
        return
    val = a**13 + (a+h)**13
    assert floor_root(val,p)**p != val, (p,t,h)


def small(p, upper):
    # Test the original sum modulo q. A row now represents gaps, not roots.
    moduli = [q for q in range(2*p+1, 3000, 2*p) if prime(q)][1:14]
    @lru_cache(None)
    def row(q, t):
        residues = {pow(y,p,q) for y in range(q)}
        flags = 0
        for h in range(q):
            a = (t-h)*((q+1)//2) % q
            if (pow(a,13,q)+pow(a+h,13,q)) % q in residues:
                flags |= 1 << h
        period = q
        while period <= GAP:
            flags |= flags << period
            period *= 2
        return flags
    count = 0
    residues = [[pow(i,p,q) for i in range(q)] for q in moduli]
    for u in range(2,upper+1):
        possible = (1 << (GAP+1))-2
        for q,table in zip(moduli,residues):
            possible &= row(q,table[u % q])
            if not possible:
                break
        while possible:
            bit = possible & -possible
            possible ^= bit
            count += 1
            check_equation(u**p,bit.bit_length()-1,p)
    return count


def enclosure(p):
    # Decimal suggests two endpoints. Directed integer arithmetic proves them.
    with localcontext() as ctx:
        ctx.prec = 270
        guess = int(Decimal(B)*(-Decimal(4096).ln()/p).exp())
    def power(x, upper):
        scale = B*EXTRA
        def multiply(a,b):
            return (a*b + (scale-1 if upper else 0))//scale
        y = scale
        base = x*EXTRA
        e = p
        while e:
            if e & 1:
                y = multiply(y,base)
            base = multiply(base,base)
            e //= 2
        return 4096*y
    lo, hi = guess-1, guess+2
    assert power(lo,True) < B*EXTRA < power(hi,False)
    return Fraction(lo,B), Fraction(hi,B)


def large(p):
    lo, hi = enclosure(p)
    stack = [(2,2*p*GAP)]
    boxes = direct = 0
    while stack:
        low, high = stack.pop()
        boxes += 1
        top = hi + Fraction(4095*GAP**2,p*low**(2*min(p,90)))
        Q = high**12
        midpoint = (lo+top)/2
        nearest = midpoint.limit_denominator(Q)
        if not lo <= nearest <= top:
            continue
        if (top-lo)*Q**2 < 1:
            den = nearest.denominator
            u = floor_root(den,12)
            if u**12 != den or not low <= u <= high:
                continue
            low = high = u
        if low == high:
            direct += 1
            for h in range(1,GAP+1):
                check_equation(low**p,h,p)
        else:
            split = isqrt(low*high)
            stack.extend([(low,split),(split+1,high)])
    return boxes,direct


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    for p,cap in [(7,238000),(11,22000)]:
        print('Small exponent, direct residue survivors:',p,small(p,cap),flush=True)
    boxes = direct = exponents = 0
    for p in range(17,300001,2):
        if prime(p):
            b,d = large(p)
            boxes += b
            direct += d
            exponents += 1
    print('Larger primes, rational intervals, directly checked roots:',exponents,boxes,direct)
