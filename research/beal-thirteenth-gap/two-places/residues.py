"""Independent exact entry and trace checks. Python 3, standard library."""
from math import comb


class Quotient:
    """(Z/m)[x]/f for a monic f, with low coefficients first."""
    def __init__(self, modulus, polynomial):
        self.m = modulus
        self.f = polynomial
        self.n = len(polynomial) - 1
        assert polynomial[-1] == 1

    def reduce(self, values):
        a = list(values)
        while len(a) > self.n:
            lead = a.pop()
            offset = len(a) - self.n
            for j, v in enumerate(self.f[:-1]):
                a[offset + j] -= lead * v
        return tuple(v % self.m for v in a + [0] * (self.n - len(a)))

    def mul(self, a, b):
        p = [0] * (len(a) + len(b) - 1)
        for i, u in enumerate(a):
            for j, v in enumerate(b):
                p[i+j] += u*v
        return self.reduce(p)

    def power(self, a, n):
        result = self.reduce([1])
        while n:
            if n & 1:
                result = self.mul(result, a)
            a = self.mul(a, a)
            n //= 2
        return result


def entry(p):
    ring = Quotient(p*p, [1]*13)
    zf = ring.power(ring.reduce([0, 1]), p)
    # If alpha is a p-th power then Frobenius(alpha) = alpha^p mod p^2.
    passed = []
    for t in range(p*p):
        alpha = ring.reduce([t, 1-t])
        frob = ring.reduce([t+(1-t)*zf[0], *((1-t)*v for v in zf[1:])])
        if ring.power(alpha, p) == frob:
            passed.append(t)
    assert passed == [0, 1]
    # Infinity: arbitrary rational-unit multiple of (1-z).
    x = ring.reduce([1, -1])
    xp = ring.power(x, p)
    fx = ring.reduce([1-zf[0], *(-v for v in zf[1:])])
    scalars = [a for a in range(p*p) if a % p and
               ring.reduce([a**p * v for v in xp]) == ring.reduce([a*v for v in fx])]
    assert not scalars
    print("finite chart", passed, "infinity scalars", scalars)


def place(p, factor):
    ring = Quotient(p, factor)
    W,U,Y = [ring.reduce(a) for a in ([6,1,-2],[2,3,1],[3,2])]
    v = ring.mul(ring.power(W,p), ring.mul(U,ring.power(Y,3*(p**3-2))))
    trace = ring.reduce([sum(row) for row in zip(v, ring.power(v,p), ring.power(v,p**2))])
    assert trace[1:] == (0,0)
    def value(x):
        return sum(a*x**i for i,a in enumerate(factor))
    norm = value(-1)*value(-2) % (p*p)
    quotient = (pow(norm,p-1,p*p)-1)//p
    print("norm, quotient, trace",norm,quotient,trace[0])
    return quotient,trace[0]


if __name__ == "__main__":
    F = [-1,3,6,-4,-5,1,1]
    for p, a, b, expected in [
        (17,[258,288,30,1],[28,288,260,1],[(7,3),(10,5)]),
        (23,[283,528,245,1],[243,528,285,1],[(9,17),(14,0)]),
    ]:
        print("p =",p)
        entry(p)
        product = [0]*7
        for i, u in enumerate(a):
            for j, v in enumerate(b):
                product[i+j] += u*v
        assert all((x-y) % (p*p) == 0 for x,y in zip(product,F))
        for f in [a,b]:
            assert all(sum(c*t**i for i,c in enumerate(f)) % p for t in range(p))
        assert [place(p,f) for f in (a,b)] == expected
