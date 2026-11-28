"""Exact Bernstein certificate for a polynomial with a shifted cyclotomic factor."""
from fractions import Fraction
from math import comb

a, b, c, t = 232, 132, 16, 5
degree = a+b+2*c+2*t
# On y+z=1 the homogeneous polynomial equals, up to the sign (-1)^b,
# 2^(a+b) y^a z^b (y^2-z^2)^c (y^2+3z^2)^t.
# j is half the exponent of y after removing y^a.
coefficients = [
    sum((-1)**(c-i)*comb(c,i)*comb(t,j-i)*3**(t-j+i)
        for i in range(max(0,j-t), min(c,j)+1))
    for j in range(c+t+1)
]
eta = Fraction(0)
for j, value in enumerate(coefficients):
    ones = a+2*j
    zeros = degree-ones
    assert 4*zeros <= 3*ones
    eta = max(eta, Fraction(2**(a+b)*abs(value), comb(degree,ones)))
assert eta < 1
print(f"{degree=}, {len(coefficients)} slots, 0 < eta <= 995/1000 is {0<eta<=Fraction(995,1000)}")
print("eta =", eta)
