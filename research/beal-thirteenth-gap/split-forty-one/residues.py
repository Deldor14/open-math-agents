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


def last_trace(p):
    ring = Quotient(p, [-1, 3, 6, -4, -5, 1, 1])
    W, U, Y = (ring.reduce(v) for v in ([6, 1, -2], [2, 3, 1], [3, 2]))
    y_inv = ring.power(Y, p**6-2)
    assert ring.mul(Y, y_inv) == ring.reduce([1])
    v = ring.mul(ring.power(W, p), ring.mul(U, ring.power(y_inv, 3)))
    theta_traces = [((13*comb(j,j//2) if j % 2 == 0 else 0) - 2**j)//2 for j in range(6)]
    value = sum(t*n for t, n in zip(theta_traces, v)) % p
    assert value == 31
    print("W^41 U / Y0^3", v, "power traces", theta_traces, "absolute trace", value)


def auxiliary():
    q = 163
    ring = Quotient(q, [1]*13)
    z = ring.reduce([0, 1])
    order = q**12 - 1
    shift = ring.mul(z, ring.power(ring.reduce([1, -1]), order-1))
    ex = order // 41
    assert order % 41 == 0
    passed = [t for t in range(q) if ring.power(
        ring.reduce([t + shift[0], *shift[1:]]), ex) == ring.reduce([1])]
    assert not passed
    print("finite residues for the extraneous unit at 163", passed)

    # w^2=w+3. A nonzero element is a square in F_(q^2) exactly
    # when its norm is a square in F_q.
    def mul(x, y):
        a,b = x
        c,d = y
        return ((a*c+3*b*d) % q, (a*d+b*c+b*d) % q)

    def curve_trace(A, B):
        total = 0
        for a in range(q):
            for b in range(q):
                x = (a,b)
                t,u = mul(x,x)
                t,u = mul(x, (t+A[0],u+A[1]))
                t,u = t+B[0],u+B[1]
                norm = (t*t+t*u-3*u*u) % q
                symbol = pow(norm,(q-1)//2,q)
                total += -1 if symbol == q-1 else symbol
        return -total

    pairs = [((13,50),(66,129)),((137,27),(22,56)),((56,1),(116,32))]
    traces = [curve_trace(A,B) for A,B in pairs]
    print("F_(163^2) traces", traces, "modulo 41", [v % 41 for v in traces])
    assert all((traces[0]-v) % 41 for v in traces[1:])


if __name__ == "__main__":
    auxiliary()
    entry(41)
    last_trace(41)
