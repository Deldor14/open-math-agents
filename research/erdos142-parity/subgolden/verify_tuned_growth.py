"""Recompute the scalar certificate by integer arithmetic, independently of Lean."""
from fractions import Fraction
from math import prod

C = 2303115151489024
M = 59**3 * 61**9
depth = 50
initial = 24178516392292583494123520
left, right = initial, 35672756411597299944259584
endpoints = [right]
lengths = []
for i in range(depth):
    mesh = 2 ** (73 - (3*i)//2)
    assert left % mesh == right % mesh == 0
    lo, hi = left // mesh, right // mesh
    x, steps = lo, 0
    while x < hi:
        # Both inequalities are precisely the fit conditions for one comparison.
        nxt = min(hi, 2*x+1-lo, (hi+1+x)//2)
        assert x < nxt <= hi
        complement = lo + hi - x
        assert nxt + complement + max(nxt, complement) <= lo + 2*hi + 1
        x, steps = nxt, steps + 1
    lengths.append(steps)
    left, right = left + right, left + 2*right + mesh
    endpoints.append(right)

budget = C - 2**45
copies, low = divmod(budget, 2**depth)
levels = [i for i in range(depth) if (low >> i) & 1] + [depth]*copies
assert sum(2**i for i in levels) == budget
assert sum(endpoints[i] for i in levels) >= M*(initial+1)
gain = Fraction(C-budget, C*2**depth*prod(lengths))
assert gain > Fraction(1, 10**123)
assert (left, right) == (17930960184279979613136592675447023779624342874,
                         29012903029086084987555223918059441665802764285)
old = Fraction(747230980351474411985551361801500529348765790,
               461814143304116035103818818074847139530008111)
assert Fraction(right+1, left) < old
assert (right+1)**2 - (right+1)*left - left**2 < 0
print(f"{depth} stages, {sum(lengths)} comparisons, gain {float(gain):.8g}")
print(f"Endpoint ratio {right}/{left}, cover uses {len(levels)} terms")
