"""Exact midpoint tests for an odd function detecting both a site and its double."""
from itertools import product


def triangle(x, p):
    # Four times a continuous odd triangular wave, evaluated on the p-point circle.
    t = x % p
    if 4*t <= p:
        return 4*t
    if 4*t <= 3*p:
        return 2*p-4*t
    return 4*t-4*p


def cyclic_test(p, m, radius):
    values = [sum((-1)**j * triangle((1 << j)*x,p) for j in range(m)) for x in range(p)]
    assert all(values[-x] == -v for x,v in enumerate(values))
    aux = range(-radius, radius+1)
    bound = max(abs(values[(x+b)%p]-values[x]) for x in range(p) for b in aux)
    patch = {x for x in range(p) if values[x]>3*bound and values[2*x%p]<-3*bound}
    assert not patch.intersection(b%p for b in aux)
    for b in aux:
        for x in patch:
            assert (2*b-x)%p not in patch
            assert (2*x-b)%p not in patch
        for c in aux:
            assert (2*b-c)%p not in patch
            assert ((b+c)*pow(2,-1,p))%p not in patch
    # Keep all conclusions exact, including the displayed mass.
    return len(patch), bound


def exhaust_interval(n):
    triples = [(x,x+q,x+2*q) for q in range(1,n) for x in range(n-2*q)]
    windows = {l:[tuple(a+j*q for j in range(l))
                  for q in range(1,n+1) for a in range(max(0,n-(l-1)*q))]
               for l in range(1,n+1)}
    maximum = [0]*(n+1)
    for labels in product(range(3), repeat=n):
        # 0 is unused, 1 is the prescribed region, 2 is the blocker.
        if any(all(labels[x]>0 for x in t) and any(labels[x]==2 for x in t) for t in triples):
            continue
        patch_size = labels.count(1)
        for l in range(1,n+1):
            if all(any(labels[x]==2 for x in window) for window in windows[l]):
                assert 2*patch_size <= n+l
                maximum[l] = max(maximum[l],patch_size)
    return maximum[1:]


if __name__ == '__main__':
    for p,m in ((4093,4),(65537,6)):
        count, bound = cyclic_test(p,m,2)
        print(f'cyclic group of order {p}, {m} terms, maximum variation {bound}, {count} protected sites')
    for n in range(3,10):
        print(f'n={n}, maxima by length: {exhaust_interval(n)}')
