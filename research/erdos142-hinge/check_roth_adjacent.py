"""Enumerate extremizers of the relevant finite phase choices and test both lifts."""
from itertools import combinations
from fractions import Fraction

SHAPES = [(0,), (0,1), (0,2), (0,4), (0,1,5), (0,4,5), (0,4,5,9)]


def free(points):
    points = set(points)
    return all(2*b-a not in points for a,b in combinations(sorted(points),2))


def weak(points, step):
    return all(abs(a+b+c-3*y) not in (0,step,2*step)
               for a,b,c in combinations(points,3) for y in (a,b,c))


def best(candidates):
    for k in range(len(candidates),-1,-1):
        if any(free(choice) for choice in combinations(candidates,k)):
            return k


def local(shape,p,q,h):
    # Relative coordinates in units t/2. Endpoints of every half-open band
    # are tested as integers, including the two extreme phases.
    return sorted({u for j in shape for u in range(32)
                   if (j-u)%2 == 0 and p*j+h <= q*u < p*j+h+3*p})


def phases():
    for p,q in [(1,2),(2,1)]:
        weights = []
        for shape in SHAPES:
            scores = [best(local(shape,p,q,h)) for h in range(2*q)]
            weights.append(Fraction(sum(scores),2*q*len(shape)))
        print('slope',Fraction(p,q),'ratios',*(str(x) for x in weights))
        assert min(weights) == (Fraction(5,8) if q==2 else 2)


def intervals():
    sets = [()]
    for x in range(14):
        sets += [s+(x,) for s in sets if free(s+(x,))]
    cases = even = copies = nonempty = 0
    for a in sets:
        n = a[-1]+1 if a else 0
        for t in range(1,9):
            if not weak(a,t):
                continue
            cases += 1
            even += t%2==0
            roots = [x for x in a if x+t in a]
            nonempty += bool(roots)
            total = 0
            for phase in range(4):
                points = []
                for x in roots:
                    # Direct enumeration of the geometric band independently
                    # of the quotient, remainder and tag formulas in Lean.
                    points.extend(y for y in range((n+1)//2+2*t) if (x-y)%t==0 and
                                  phase*t <= 4*y-2*x < (phase+5)*t)
                assert len(set(points))==len(points) and free(points)
                total += len(points)
            assert total==5*len(roots)
            copies += total
    print('weak sets and steps',cases,'even',even,'with roots',nonempty,'tagged sites',copies)


if __name__=='__main__':
    phases()
    intervals()
