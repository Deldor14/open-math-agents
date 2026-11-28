"""Exact boundary checks for the separating-energy obstruction. Standard library only."""
from fractions import Fraction as Q
from itertools import product

# (a+b*sqrt(2))/d is implemented in the inherited exact polygon verifier.
# Pass its directory on the command line (verifica_parametro.py and verifica_poligono.py).
import sys
from pathlib import Path
sys.path.insert(0, str(Path(sys.argv[1]).resolve()))
from verifica_parametro import Cell, F, G, J, R, Surd, V, half, q

left, right = Q(1, 32), Q(1, 16)
assert Q(5, 64) < J < F < V < G < R
assert 1 < q < 2
plus, minus = Cell(0, 0, '+'), Cell(0, 0, '-')

def witness(u, eps):
    d = 8 * eps / q
    lx, hx = plus.edges(half + u - d)
    ly, hy = minus.edges(half + u)
    lz, hz = minus.edges(half + u + d)
    tx, tz = lx + 2*eps, lz + 2*eps
    ty = (tx+tz)/2
    assert ty == hy-2*eps
    assert lz+eps <= tz <= hz-eps and lx+eps <= tx <= hx-eps
    assert ly+eps <= ty <= hy-eps
    a,b,c = 2*tx-half, 2*ty+half, 2*tz+half
    assert a+c == 2*b-1
    for v in (a,b,c):
        assert -half <= v <= half
    return a,b,c

# All tests before the squared inequality are affine on this parameter rectangle.
for u,eps in product((left,right),(Q(0),Q(1,16384))):
    a,b,c = witness(u,eps)
    assert (1+a)*(1+a)+(1+c)*(1+c)-2*(1+b)*(1+b) <= -1

# A common rectangle in the positive lobe for the integrated variance bound.
for u in (left,right):
    low, high = plus.edges(half+u)
    assert low + Q(1,16384) < Q(1,8) < Q(1,4) < high-Q(1,16384)

# The triangular weights in the discrete second-difference identity.
for k in range(1,129):
    coeff = [0]*(2*k+1)
    for j in range(-k+1,k):
        a = k-abs(j)
        for shift, weight in ((-1,1),(0,-2),(1,1)):
            coeff[j+shift+k] += a*weight
    expected = [0]*(2*k+1)
    expected[0], expected[k], expected[-1] = 1, -2, 1
    assert coeff == expected
    assert sum(k-abs(j) for j in range(-k+1,k)) == k*k
print('Exact affine corner checks, rectangle, and 128 discrete stencils passed.')
