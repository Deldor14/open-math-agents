"""Pure-integer checks of the tame-prime sieve and the 2-adic logarithm residues."""
from functools import reduce
from operator import xor
from math import isqrt


def multiply_cyclotomic(a,b,q):
    c = [0]*23
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            c[i+j] += x*y
    # x^12=-(1+x+...+x^11).
    for i in range(22,11,-1):
        for j in range(i-12,i):
            c[j] -= c[i]
    return [v % q for v in c[:12]]


def power_cyclotomic(a,e,q):
    result = [1]+[0]*11
    while e:
        if e & 1:
            result = multiply_cyclotomic(result,a,q)
        e //= 2
        if e:
            a = multiply_cyclotomic(a,a,q)
    return result


def tame(q):
    assert all(q % d for d in range(2,isqrt(q)+1)) and q % 11 == 1
    f = next(j for j in range(1,13) if pow(q,j,13)==1)
    exponent = (q**f-1)//11
    # Precompute powers of the binomial once per projective parameter.
    inf = power_cyclotomic([1,-1]+[0]*10,exponent,q)
    assert any(inf[1:])
    valid = [u for u in range(q) if power_cyclotomic([u,1-u]+[0]*10,exponent,q)==[1]+[0]*11]
    assert valid == [0,1]
    print(q,"cyclotomic affine parameters",valid,"infinite parameter excluded")
    if q==23:
        return
    places = []
    for r in range(q):
        if (r**3+r*r-4*r+1) % q:
            continue
        ts = [t for t in range(1,q) if pow(t,11,q)==2*r % q]
        if len(ts)!=11:
            continue
        s = (r*r-r+1) % q
        roots = [-4*s*pow(t,-2,q) % q for t in ts]
        assert len(set(roots))==11
        candidates = []
        for v in range(q):
            if pow(v,11,q)!=1:
                continue
            x = 4*s*v % q
            signs = [(x-th if x!=th else 11*th**10)%q for th in roots]
            candidates.append(sum(pow(z,(q-1)//2,q)==q-1 for z in signs))
        assert len(candidates)==11 and min(candidates)>0
        places.append((r, sorted(candidates)))
    assert len(places)==1
    print(q,"split place and nonsquare counts",places[0])


def mul8(x,y):
    result = 0
    while y:
        if y & 1:
            result ^= x
        x <<= 1
        if x & 8:
            x ^= 13  # r^3+r^2+1
        y >>= 1
    return result


def pow8(x,k):
    result = 1
    for _ in range(k):
        result = mul8(result,x)
    return result


def pack(vector):
    return sum(v << (3*i) for i,v in enumerate(vector))


def logspace():
    tiny = []
    for a in [1,3,5,7]:
        for h in [1,2,4]:
            tiny.append(pack([mul8(pow8(a,i),h) ^
                              (mul8(pow8(a,i-1),mul8(h,h)) if i%2 else 0)
                              for i in range(5)]))
    tiny.extend(pack([0,0,0,0,h]) for h in [1,2,4])
    def logs(word):
        return reduce(xor,(v for i,v in enumerate(tiny) if word & (1<<i)),0)
    assert len({logs(i) for i in range(2**15)})==2**15
    basis = [logs(i) for i in [8336,29771,9056]]  # exact GP localization
    span = sorted({reduce(xor,(v for j,v in enumerate(basis) if i & (1<<j)),0)
                   for i in range(8)})
    target = pack([2]*5)
    assert len(span)==8 and target not in span
    print("Selmer log/2 residues",span,"excluded primitive direction",target)


if __name__ == "__main__":
    for prime in (23,1607,1871):
        tame(prime)
    logspace()
