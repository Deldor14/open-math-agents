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
    assert value == 5
    print("W^11 U / Y0^3", v, "power traces", theta_traces, "absolute trace", value)


if __name__ == "__main__":
    entry(11)
    last_trace(11)
