"""Verify a table of split-prime certificates using just the Python standard library."""
from math import gcd, isqrt, lcm, prod
from pathlib import Path
import sys


def divisors(n):
    """Distinct prime divisors by trial division."""
    d = 2
    while d*d <= n:
        if not n%d:
            yield d
            while not n%d:
                n //= d
        d += 1 if d==2 else 2
    if n>1:
        yield n


def cyclic(q, n):
    for x in range(2,q):
        root = pow(x,(q-1)//n,q)
        if all(pow(root,n//d,q)!=1 for d in divisors(n)):
            return root
    raise AssertionError('no generator')


def projective(p,q):
    m = (q-1)//p
    z = cyclic(q,7)
    roots = [pow(z,i,q) for i in [2,5,3,4,1,6]]
    offsets = [zj-1 for zj in roots]
    d1,d2 = offsets[:2]
    # Use s=b/(a+b), including s=0 (b=0) and s=1 (a=0).
    candidates = {-pow(d1,-1,q)%q, -pow(d2,-1,q)%q}
    h, step = 1, cyclic(q,m)
    for _ in range(m):
        if (d1-h*d2)%q:
            candidates.add((h-1)*pow(d1-h*d2,-1,q)%q)
        h = h*step%q
    for s in candidates:
        values = [(1+s*d)%q for d in offsets]
        chars = [pow(w,m,q) for w in values]
        if any(u and v and u!=v for u,v in zip(chars[::2],chars[1::2])):
            continue
        if prod(chars)%q not in [0,1]:
            continue
        assert s in (0,1),(p,q,s)
    # Decide if the second unit character vector is a power of the first.
    u = [pow(1+r,m,q) for r in roots]
    v = [pow(1+r*r,m,q) for r in roots]
    j = next(i for i in range(6) if u[i]!=1)
    size = isqrt(p)+1
    small = {pow(u[j],d,q):d for d in range(size)}
    target = v[j]
    stride = pow(u[j],-size,q)
    for k in range(size+1):
        if target in small:
            exp = size*k+small[target]
            assert any(pow(a,exp,q)!=b for a,b in zip(u,v))
            return
        target = target*stride%q
    raise AssertionError('invalid character')


def square_root(a,q):
    """Tonelli–Shanks for a verified nonzero quadratic residue."""
    n = q-1
    k = 0
    while n%2 == 0:
        n //= 2
        k += 1
    g = next(g for g in range(2,q) if pow(g,(q-1)//2,q)==q-1)
    c = pow(g,n,q)
    x,b = pow(a,(n+1)//2,q),pow(a,n,q)
    while b!=1:
        i = next(i for i in range(1,k) if pow(b,2**i,q)==1)
        h = pow(c,2**(k-i-1),q)
        x,b,c,k = x*h%q,b*h*h%q,h*h%q,i
    assert x*x%q == a
    return x


def order_certificate(q, curve, trace):
    A,B,C = curve
    def rhs(x):
        return (((x+A)*x+B)*x+C)%q
    def add(P,Q):
        if P is None or Q is None:
            return P if Q is None else Q
        x,y = P
        u,v = Q
        if x==u:
            if (y+v)%q==0:
                return None
            slope = (3*x*x+2*A*x+B)*pow(2*y,-1,q)%q
        else:
            slope = (v-y)*pow(u-x,-1,q)%q
        z = (slope*slope-A-x-u)%q
        return z,(slope*(x-z)-y)%q
    def times(n,P):
        out = None
        while n:
            if n%2:
                out = add(out,P)
            n //= 2
            if n:
                P = add(P,P)
        return out
    width = isqrt(4*q)
    n = q+1-trace
    low,high = q+1-width,q+1+width
    assert low<=n<=high
    factors = list(divisors(n))
    modulus = 1
    for x in range(min(100,q)):
        a = rhs(x)
        if not a or pow(a,(q-1)//2,q)!=1:
            continue
        point = x,square_root(a,q)
        assert times(n,point) is None
        order = n
        for d in factors:
            while order%d==0 and times(order//d,point) is None:
                order //= d
        modulus = lcm(modulus,order)
        if high//modulus-(low-1)//modulus==1:
            return
    squares = bytearray(q)
    for y in range(1,(q+1)//2):
        squares[y*y%q] = 1
    actual = 1+sum(1 if (v:=rhs(x))==0 else 2*squares[v] for x in range(q))
    assert actual==n,(q,n,actual)


def main():
    rows = [list(map(int,line.split())) for line in Path(sys.argv[1]).read_text().splitlines()]
    bound = int(sys.argv[2]) if len(sys.argv)>2 else 20000
    assert [r[0] for r in rows]==[p for p in range(11,bound+1) if list(divisors(p))==[p]]
    for p,q,a,b in rows:
        assert list(divisors(q))==[q] and (q-1)%(14*p)==0
        projective(p,q)
        order_certificate(q,(-1,-2,1),a)
        order_certificate(q,(-4,-11,43),b)
        assert (a-b)%p!=0
    print(len(rows),'split-prime certificates and both elliptic orders verified')


if __name__=='__main__':
    main()
