"""Exact endpoint certificates for the mixed septic full-order estimates."""
from fractions import Fraction as F
from math import factorial


def exp_bounds(x, terms=100):
    """Taylor sum and geometric majorant for its positive tail."""
    assert 0 < x < terms + 2
    low = sum(x**j / factorial(j) for j in range(terms+1))
    first = x**(terms+1) / factorial(terms+1)
    high = low + first / (1 - x/F(terms+2))
    return low, high


# 3.36 < log(29), log(39) > 3.65, log(800000) < 13.6,
# and log(2000000) < 14.51. Upper bounds for pi use 22/7.
assert exp_bounds(F(336,100))[1] < 29
assert exp_bounds(F(365,100))[1] < 39
assert exp_bounds(F(136,10))[0] > 800000
assert exp_bounds(F(1451,100))[0] > 2000000
assert exp_bounds(F(10))[1] < 800000
assert F(1285,100)*F(22,7)/2/F(336,100)+F(1,2) < F(655,100)
assert 20/F(336,100) < F(655,100)
assert F(257,10)*F(314,100)>80
assert F(1705,100)-3*F(365,100) <= F(61,10)
assert 7*(F(11,7))**6 < 29**2
assert 7*(F(11,7))**12 < 29**3

def squared_bound(logn):
    return 354*(3*logn+F(61,10))**2

assert squared_bound(F(136,10))+2 < 800000
anchor = 2000000
assert 10**25 > 11**24 and 2**10 < 11**3
assert anchor**24 > 1000000**25
assert anchor**3 < 80**10
assert squared_bound(F(1451,100))+2+2*80*15 < 1000000
assert 2*squared_bound(F(1451,100))+3 < anchor
assert all(29**(p-1) > (6*p)**6 for p in (11,13,17))
print("exact rational bounds passed at 800000 and 2000000")
