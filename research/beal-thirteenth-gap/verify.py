"""Exact certificate for coprime positive thirteenth powers with gap <= 1000.

Run with Python 3.8+ and assertions enabled. Uses only the standard library.
"""
from fractions import Fraction
from math import comb, factorial, gcd, isqrt

H = 1000
P_LIMIT = 300000
S = 1 << 800
COEFF = [comb(13, j) for j in range(0, 13, 2)]
ERROR = 400


def primes(limit):
    sieve = bytearray(b'\1') * (limit + 1)
    sieve[:2] = bytes(2)
    for n in range(2, isqrt(limit) + 1):
        if sieve[n]:
            sieve[n*n::n] = bytes((limit - n*n)//n + 1)
    return [j for j in range(limit + 1) if sieve[j]]


def root(n, k):
    low, high = 0, 1 << ((n.bit_length() + k - 1) // k)
    while low + 1 < high:
        mid = (low + high) // 2
        if mid**k <= n:
            low = mid
        else:
            high = mid
    return high if high**k == n else low


def original(u, p, h):
    t = u**p
    if t <= h or (t-h) % 2:
        return False
    a, b = (t-h)//2, (t+h)//2
    if gcd(a, b) > 1:
        return False
    total = a**13 + b**13
    return root(total, p)**p == total


def check_small(p, cap):
    # The q-bit word records the admissible residues of u modulo q.
    # Replication by shifts gives every u up to and including cap.
    tables = []
    for q in [q for q in primes(1500) if q % (2*p) == 1][:12]:
        powers = {pow(v, p, q)*4096 % q for v in range(q)}
        up = [pow(u, p, q) for u in range(q)]
        words = []
        for h in range(q):
            coeff = [c*pow(h, 2*i, q) % q for i, c in enumerate(COEFF)]
            good = {}
            for t in set(up):
                value = sum(c*pow(t, 12-2*i, q) for i,c in enumerate(coeff))
                good[t] = value % q in powers
            word = sum(1 << u for u,t in enumerate(up) if good[t])
            step = q
            while step <= cap:
                word |= word << step
                step *= 2
            words.append(word & ((1 << (cap+1))-1))
        tables.append((q, words))
    count = 0
    for h in range(1, H+1):
        candidates = (1 << (cap+1))-4
        for q, words in tables:
            candidates &= words[h % q]
        while candidates:
            bit = candidates & -candidates
            candidates -= bit
            u = bit.bit_length() - 1
            count += 1
            assert not original(u, p, h), (p, u, h)
    return count


def convergents(a, b, limit):
    h2,h1,k2,k1 = 0,1,1,0
    while b:
        q, remainder = divmod(a, b)
        h2,h1 = h1, q*h1+h2
        k2,k1 = k1, q*k1+k2
        if k1 > limit:
            return
        yield h1,k1
        a,b = b,remainder


def log_scale():
    lo = sum((Fraction(2, (2*j+1)*3**(2*j+1)) for j in range(270)), Fraction())
    hi = lo + Fraction(3, 3**541)
    assert int(S*lo) == int(S*hi)
    return int(S*lo)


def center(p, log2):
    h = 12*log2//p
    assert 2*h < S and factorial(161) > S
    total = term = S
    for j in range(1,161):
        term = term*h//(S*j)
        total += -term if j % 2 else term
        if term == 0:
            break
    return total


def check_large():
    log2 = log_scale()
    assert 4*ERROR*(2*P_LIMIT*H)**24 < S
    counts = [0,0,0,0]
    for p in primes(P_LIMIT):
        if p < 17:
            continue
        counts[0] += 1
        z = center(p, log2)
        threshold = 2
        while p*threshold**(2*min(p,50)-24) <= 4*4095*H**2:
            threshold += 1
        for u in range(2, threshold):
            for h in range(1, H+1):
                counts[1] += 1
                assert not original(u,p,h), (p,u,h)
        for v,q in convergents(z,S,(2*p*H)**12):
            counts[2] += 1
            if q < threshold**12:
                continue
            s = isqrt(q)
            if s*s != q:
                continue
            w = isqrt(s)
            if w*w != s:
                continue
            u = root(w,3)
            if u**3 != w:
                continue
            counts[3] += 1
            # Exact check only if the convergent has the required precision.
            # Capping the exponent enlarges the admissible interval.
            radius = p*u**(2*min(p,96))
            if S*v <= (z-ERROR)*q or (S*v-(z+ERROR)*q)*radius > S*q*4095*H**2:
                continue
            for h in range(1,H+1):
                assert not original(u,p,h), (p,u,h,v)
    return counts


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    for exponent, bound in [(7,238*H),(11,22*H)]:
        print('Small exponent, root cap, residue survivors:', exponent, bound,
              check_small(exponent,bound), flush=True)
    print('Larger primes, direct pairs, convergents, twelfth-power denominators:',
          *check_large())
