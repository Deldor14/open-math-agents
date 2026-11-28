"""Exact certificate for nearby primitive eleventh powers. Python 3, no packages."""
from decimal import Decimal, localcontext
from math import gcd, isqrt

GAP = 1000
MAX_P = 200000
SCALE = 1 << 704


def ceil_div(x, y):
    return -(-x // y)


def integer_root(x, k):
    low, high = 0, 1 << ceil_div(x.bit_length(), k)
    while high - low > 1:
        mid = (low + high) // 2
        if mid ** k <= x:
            low = mid
        else:
            high = mid
    return high if high ** k <= x else low


def primes(limit):
    prime = bytearray([1]) * (limit + 1)
    for i in range(2, isqrt(limit) + 1):
        if prime[i]:
            prime[i*i::i] = bytes((limit-i*i)//i + 1)
    return (i for i in range(7, limit + 1) if prime[i] and i != 11)


def dyadic_power(n, p):
    lo = hi = SCALE
    a = b = n
    while p:
        if p % 2:
            lo, hi = lo*a//SCALE, ceil_div(hi*b, SCALE)
        a, b = a*a//SCALE, ceil_div(b*b, SCALE)
        p //= 2
    return lo, hi


def simplest(a, b, c, d):
    """A fraction minimizing numerator and denominator on the closed interval."""
    prefix = []
    while True:
        integer = ceil_div(a, b)
        if integer*d <= c:
            n, q = integer, 1
            break
        k = a // b
        prefix.append(k)
        a, b, c, d = d, c-k*d, b, a-k*b
    for k in reversed(prefix):
        n, q = k*n+q, n
    return n, q


def original_by_gap(u, p):
    total = u**p
    tests = 0
    for gap in range(1, min(GAP, total-2)+1, 2):
        if gcd(gap, u) != 1:
            continue
        a = (total-gap)//2
        value = a**11 + (total-a)**11
        root = integer_root(value, p)
        assert root**p != value, (u, p, gap)
        tests += 1
    return tests


def eliminate(u, p, v):
    """A monotone exact comparison with every allowable positive gap."""
    total = u**p
    target = (u*v)**p
    low, high = 0, (min(GAP, total-2)-1)//2
    while low <= high:
        mid = (low+high)//2
        gap = 2*mid+1
        a = (total-gap)//2
        value = a**11 + (total-a)**11
        if value == target:
            assert gcd(gap, u) != 1, (u, p, v, gap)
            return
        if value < target:
            low = mid+1
        else:
            high = mid-1


def run():
    if not __debug__:
        raise RuntimeError("Run without -O: assertions are part of this certificate.")
    quintic = sum(original_by_gap(u, 5)
                  for u in range(3, integer_root(1024*GAP**4, 10)+1, 2) if u % 11)
    num_primes = boxes = singletons = tests = gap_checks = 0
    with localcontext() as ctx:
        ctx.prec = 240
        log_alpha = -Decimal(1024).ln()
        for p in primes(MAX_P):
            num_primes += 1
            guess = int((log_alpha / p).exp() * SCALE)
            left, right = guess-4096, guess+4096
            assert 1024*dyadic_power(left,p)[1] < SCALE
            assert SCALE < 1024*dyadic_power(right,p)[0]
            stack = [(3, 2*p*GAP-1)]
            while stack:
                u, w = stack.pop()
                boxes += 1
                # All reduced v/u^10 in this box obey the following closed interval.
                den = p*u**(2*min(p, 256))
                upper = right + ceil_div(SCALE*1023*GAP**2, den)
                if u == w:
                    if u % 2 == 0 or u % 11 == 0:
                        continue
                    singletons += 1
                    q = u**10
                    n0 = max(1, ceil_div(q*left, SCALE))
                    n1 = min(q-1, q*upper//SCALE)
                    if n1-n0 > GAP and p < 100:
                        gap_checks += original_by_gap(u,p)
                    else:
                        for n in range(n0, n1+1):
                            if gcd(n,u) == 1:
                                tests += 1
                                eliminate(u,p,n)
                    continue
                bound = w**10
                if (upper-left)*bound**2 < SCALE:
                    n, q = simplest(left,SCALE,upper,SCALE)
                    assert left*q <= SCALE*n <= upper*q
                    if q <= bound:
                        root = integer_root(q,10)
                        if root**10 == q and u <= root <= w and root%2 and root%11:
                            tests += 1
                            eliminate(root,p,n)
                    continue
                mid = isqrt(u*w)
                assert u <= mid < w
                stack.extend(((u,mid),(mid+1,w)))
    print("Maximum absolute difference:", GAP)
    print("Prime exponents >=7 excluding 11:", num_primes)
    print("Root boxes checked / odd eligible singletons:", boxes, singletons)
    print("Exact numerator tests / individual gap tests at p>=7:", tests, gap_checks)
    print("Individual primitive gap tests at p=5:", quintic)
    print("Remaining primitive candidates: 0")


if __name__ == "__main__":
    run()
