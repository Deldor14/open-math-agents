"""Finite analogues of the half-fibre projection and its loss-of-mass estimate."""
from fractions import Fraction as Q
from itertools import product
from random import Random

def subsets(p):
    return [[i for i in range(p) if (mask >> i) & 1]
            for mask in range(1, 1 << p)]

def finite_sums():
    count = 0
    for p in (3, 5, 7):
        sets = subsets(p)
        for a,b in product(sets, repeat=2):
            sums = {(x+z)%p for x in a for z in b}
            assert len(sums) >= min(p,len(a)+len(b)-1)
            if len(a)+len(b)>p:
                assert len(sums)==p
            count += 1
    return count

def finite_quantiles():
    rng = Random(142)
    checked = 0
    for p in (7,11,17,31):
        for _ in range(350):
            sizes = [rng.randint((p-1)//2,p) for _ in range(3)]
            a,b,c = [rng.sample(range(p),size) for size in sizes]
            f,g = [{x:rng.randrange(10) for x in u} for u in (a,b)]
            # Twice the middle score, maximized pointwise under unit cost.
            twice = {y:min((f[x]+g[(2*y-x)%p]-1 for x in a
                            if (2*y-x)%p in g), default=30) for y in c}
            fa,ga = [sorted(h.values(),reverse=True) for h in (f,g)]
            for r in range(min(len(a),len(b))):
                # Cauchy-Davenport on a prime grid has a one-point correction.
                holes = max(0,p+1-len(a)-len(b)+2*r)
                high = sum(t>fa[r]+ga[r]-1 for t in twice.values())
                assert high <= holes
                checked += 1
    return checked

def constants():
    for k in range(30):
        e = Q(1,13)
        levels = [Q(0)]
        for _ in range(k):
            levels.append(2*(levels[-1]+e))
        assert levels[-1] == 2*e*(2**k-1)
    root_upper = Q(14142136,10**7)
    assert root_upper**2>2
    area_lower = (17-6*root_upper)/28
    assert (Q(53,320)+Q(1,500))**2<area_lower**3
    assert Q(2,125000)==Q(1,250)**2
    assert Q(53,320)==Q(53,160)/2

if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled.')
    count = finite_sums()
    steps = finite_quantiles()
    constants()
    print(f'{count} sumsets; {steps} energy-quantile comparisons; exact threshold verified.')
