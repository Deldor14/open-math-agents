"""Exact Collatz bounds for the three-term interval child operator."""
from fractions import Fraction as F

N = 128


class LinearProfile:
    def __init__(self, nodes):
        assert len(nodes) == N+1 and min(nodes)>0
        self.nodes = list(nodes)
        self.prefix = [F(0)]
        for left, right in zip(nodes, nodes[1:]):
            self.prefix.append(self.prefix[-1] + F(left+right, 2*N))

    def primitive(self, x):
        x = F(x)
        i = int(x*N)
        if i == N:
            return self.prefix[i]
        t = x*N-i
        left, right = self.nodes[i:i+2]
        return self.prefix[i] + (left*t + (right-left)*t*t/2)/N

    def value(self, x):
        x = F(x)
        i = int(x*N)
        if i == N:
            return self.nodes[i]
        t = x*N-i
        return (1-t)*self.nodes[i] + t*self.nodes[i+1]

    def child_operator(self, x):
        a = self.primitive
        return (a(1)/2 + a((1+x)/2)-a(x/2)
                + a(min(2*x, 1))-a(max(0, 2*x-1)))


def enclosure(profile):
    lower, upper = None, None
    for i in range(2*N):
        x = F(i, 2*N)
        y = F(i+1, 2*N)
        z = (x+y)/2
        v0, v1, v2 = map(profile.child_operator, (x,z,y))
        # Exact quadratic Bernstein coefficients on this half-cell.
        vals = (v0, 2*v1-(v0+v2)/2, v2)
        ratios = [a/profile.value(t) for a,t in zip(vals,(x,z,y))]
        lower = min(ratios) if lower is None else min(lower, *ratios)
        upper = max(ratios) if upper is None else max(upper, *ratios)
    return lower, upper


def main():
    nodes = [10**6]*(N+1)
    for _ in range(16):
        profile = LinearProfile(nodes)
        values = [profile.child_operator(F(i,N)) for i in range(N+1)]
        nodes = [round(10**6*v/max(values)) for v in values]
    lo, hi = enclosure(LinearProfile(nodes))
    assert isinstance(lo,F) and isinstance(hi,F)
    denominator = 10**6
    print('Child-operator bounds in millionths:',
          (lo*denominator).__floor__(), (hi*denominator).__ceil__())


if __name__ == '__main__':
    main()
