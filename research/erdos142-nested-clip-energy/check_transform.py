"""Exact rational checks of same-cell, crossing and downward midpoint costs."""
from bisect import bisect_right
from collections import Counter
from fractions import Fraction as Q
from itertools import product

def local(x, knots):
    i=bisect_right(knots,x)-1
    return i,min(x-knots[i],knots[i+1]-x)

def transform(x,w,g):
    return x*x+w*w*(1/(2-g)-1)/5

def main():
    knots = [Q(0),Q(1,8),Q(3,8),Q(1,2),Q(7,8),Q(1)]
    points = [Q(i,24) for i in range(1,24) if Q(i,24) not in knots]
    scores=[Q(0),Q(1,3),Q(2,3),Q(1)]
    counts=Counter()
    for ix,x in enumerate(points):
        for z in points[ix:]:
            for carry in (0,1):
                y=(x+z-carry)/2
                if y<=0 or y>=1 or y in knots:
                    continue
                i,wx=local(x,knots);j,wz=local(z,knots);k,wy=local(y,knots)
                same=carry==0 and i==j==k
                for a,b,c in product(scores,repeat=3):
                    d=min(Q(1),a+b-2*c) if same else Q(1)
                    if d<0:continue
                    defect=transform(x,wx,a)+transform(z,wz,b)-2*transform(y,wy,c)
                    assert defect >= (x-z)**2/4+wy**2*d/20
                    counts['downward' if carry else 'within' if same else 'crossing']+=1
    print(dict(counts),sum(counts.values()),'exact midpoint comparisons')

if __name__=='__main__':
    if not __debug__:raise RuntimeError('Run with assertions enabled.')
    main()
