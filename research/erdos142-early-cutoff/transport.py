"""Independent exact checks of the signed affine widening and its integrated cost."""
from fractions import Fraction as Q
from itertools import product
from random import Random


def contained(point, lo, hi, den):
    # Use 4*den ticks and sample each physical half-cell at its midpoint.
    return (point-4*lo) % (4*den) < 4*(hi-lo)


def allowed(point, lower, partner, den):
    lo,hi = lower
    if contained(2*point,2*lo,2*hi,den):
        return False
    if partner is not None:
        left,right = partner
        if contained(point,-right,-left,den):
            return False
    return True


def check_circles():
    rng = Random(142317)
    counts = [0,0,0]
    for den in (12,18,24):
        for _ in range(5000):
            alpha,beta = rng.randrange(4),rng.randrange(4)
            f,g = rng.randrange(-3,4),rng.randrange(-3,4)
            left,other = rng.randrange(-den,2*den),rng.randrange(-den,2*den)
            lo = (left,left+rng.randrange(1,den//2+1))
            raw = (other,other+rng.randrange(1,den//2+1))
            new = (lo[0]-beta*f,lo[1]+alpha*f)
            peer = (raw[0]-beta*g,raw[1]+alpha*g)
            if not (0 <= new[1]-new[0] <= den//2 and 0 <= peer[1]-peer[0] <= den//2):
                continue
            use = rng.choice([True,False])
            loss = sum(allowed(t,lo,raw if use else None,den) and
                       not allowed(t,new,peer if use else None,den) for t in range(1,4*den,2))
            budget = (2*max(f,0)+(max(g,0) if use else 0))*(alpha+beta)
            assert Q(loss,2) <= budget
            counts[0] += 1
            counts[1] += int(f<0 and alpha+beta>0)
            counts[2] += int(use and g>0 and alpha+beta>0)
    return counts


def integrate_linear(fn, start, end, knot):
    pts = sorted({start,end,min(max(start,knot),end)})
    return sum((v-u)*(fn(u)+fn(v))/2 for u,v in zip(pts,pts[1:]))


def check_ramps():
    n=0
    for j,i in product(range(1,51),range(50)):
        T=Q(j,100)
        c=T*i/50
        z=max(0,2*T-Q(1,2))
        slope=lambda u: (u-c)/(T-c)
        first=integrate_linear(lambda u:abs(slope(u)),Q(0),T,c)
        second=integrate_linear(lambda u:max(0,slope(u)),Q(0),z,c)
        expected=(c*c+(T-c)**2+max(0,z-c)**2)/(2*(T-c))
        assert first+second==expected
        n+=1
    return n


if __name__ == '__main__':
    print('Circle cases, strict lower shrinkages, widened terminal tests:',check_circles())
    print('Exact piecewise-affine costs:',check_ramps())
