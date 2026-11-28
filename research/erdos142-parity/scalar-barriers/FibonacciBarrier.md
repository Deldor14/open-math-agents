# A Fibonacci obstruction for scalar bounds on the interval Roth number

Let R(m) denote the actual maximum size of a three-term-progression-free subset
of [1,m]. There is a continuous nondecreasing function F on the nonnegative
reals, positive off zero, with F(1)=F(987/610)=1, satisfying, for all
nonnegative real x,y and all positive integers m,

    F(x+y) ≤ F(x)+F(y) ≤ F(x+y+max(x,y)),
    R(m) F(x) ≤ F((2m−1)x).

The numbers in the second inequality are the genuine Roth numbers. Thus these
properties allow a plateau on the whole interval [1,987/610]. This is an
obstruction to proving uniform strict growth at that dilation from the
displayed properties alone. It gives no plateau for R itself.

With the digit condition omitted, for every λ below the golden ratio and
above one, such a function can be made constant on [1,λ]. Each individual
function in this family is between two positive multiples of x, equals a
linear function near zero, and has a limiting positive slope at infinity.
The all-scale positive estimate at F₁₁₂/F₁₁₁ uses additional information
about large digit sets. [Positive estimate](../long-growth/LongGrowth.md).

## A binary capacity

Let F₀=0, F₁=1 denote Fibonacci numbers in subscripts. Set
wᵢ=F₂ᵢ₊₂, so the weights start 1,3,8,21,55,144,377,987.
Choose an integer s≥1 and put M=2ˢ and W=wₛ. For j≥0 write j=Mh+b with
0≤b<M and binary digits bᵢ, and define

    A(j)=hW+Σ_{i<s} bᵢwᵢ.

Thus A(j+M)=A(j)+W. Write cᵢ=wᵢ−2wᵢ₋₁ for i≥1.
Then A(j)=j+Σ_{1≤i≤s}cᵢ floor(j/2ⁱ). This follows by expanding the
binary digits as differences of consecutive floors. The recurrence gives
cᵢ=F₂ᵢ₋₁ and Σ_{i=1}^{h+1}cᵢ=wₕ. The following estimates hold for i≤j:

    A(i)+A(j) ≤ A(i+j),
    A(i+j+1) ≤ A(i)+2A(j)+1.

The first follows from the floor formula. For the second, after taking out
A(i)+A(j)+1, each possible binary carry contributes at most cᵣ.
If 2ʰ≤j<2ʰ⁺¹ only indices r≤h+1 can carry. For h<s the total carry is
at most wₕ≤A(j). For h≥s it is at most wₛ₋₁≤A(j). The case j=0 is
immediate. The two inequalities and the evaluation A(2ˢ)=wₛ are proved
for arbitrary s in FibonacciCarry.lean.

## The continuous function

Construct G on each interval [A(j),A(j+1)] by increasing with slope one
from j to j+1 on [A(j),A(j)+1] and staying at j+1 for the rest.
A(j+1)≥A(j)+1 ensures consistency. In particular G(x+W)=G(x)+M,
and (M/W)x≤G(x)≤x, since each wᵢ/2ⁱ≤W/M. One can also read these
bounds on the two endpoints of each linear segment.

For real u=j+a, j≥0 integer and 0≤a<1, the largest x with G(x)≤u
is A(j)+a. The first inequality on A and the fact that A increases
by at least one per integer show that this upper inverse is superadditive.
Consequently G(x+y)≤G(x)+G(y).

For 0<u=j+a with 0<a≤1, the least x with G(x)≥u is p(u)=A(j)+a.
Take u=i+a≤v=j+b with 0<a,b≤1. If a+b≤1 then
A(i+j)≤A(i)+2A(j) by the second carry inequality and strict increase.
If a+b>1 use A(i+j+1)≤A(i)+2A(j)+1 directly. In both cases
p(u+v)≤p(u)+2p(v). Taking u=G(x), v=G(y) for 0<x≤y proves
G(x)+G(y)≤G(x+2y). Zero inputs follow by monotonicity.

G=M on [A(M−1)+1,W]=[F₂ₛ₊₁,F₂ₛ₊₂]. Here we used
1+Σ_{i<s}F₂ᵢ₊₂=F₂ₛ₊₁. Normalize by setting F(x)=G(F₂ₛ₊₁ x)/M.
These even-over-odd Fibonacci ratios increase to the golden ratio.
This proves the assertion without the digit condition.

## Checking all genuine digit multipliers for s=7

Now M=128, W=987. For fixed integers 1≤r≤L, the following finite criterion
is equivalent to G(Lx)≥rG(x) for every x≥0:

    r A(rj+l) ≤ rL A(j)+L l       (0≤j<M, 0≤l<r).

Indeed the inequality for G is equivalent to p(ru)≤L p(u) for u>0.
Write u=j+a with 0<a≤1. On l/r<a≤(l+1)/r the difference
p(ru)−Lp(u)=A(rj+l)−L A(j)−l+(r−L)a reaches its supremum at the
left limit. Multiplying that value by r gives the criterion. Replacing
j by j+M subtracts r(L−r)W from the left-minus-right difference in the
criterion, so a single period suffices.

We use upper bounds for R at seven lengths. At lengths 1,3,8,29,50,88,186
the values are 1,2,4,11,16,24,40. The previously published exhaustive
calculations are tabulated by Gasarch, Glenn and Kruskal.
[Primary source, Appendix II](https://www.cs.umd.edu/~gasarch/papers/3apI.pdf).

For m≤340 form an upper bound U(m) with U(0)=0 and
U(m)=min(R(b)+U(max(0,m−b))) over the seven lengths b. Monotonicity
and subadditivity of R justify this induction even if b>m. For 1≤m≤154
the checker applies the finite criterion with r=U(m), L=2m−1. It verifies
484,096 integer comparisons. For 155≤m≤340 it checks the simpler
W U(m)≤M(2m−1). The latter extends to every m≥155 by adding 186:
R(m+186)≤R(m)+40 and 40W≤372M. The bounds (M/W)x≤G(x)≤x now yield
the required digit inequality for the entire tail. The case m=1 is equality.

Run `python3 verify_fibonacci_barrier.py` with assertions enabled.
The new exact checks use the published seven Roth numbers as inputs.
They do not rerun the published exhaustive searches. Apart from the binary
carry lemmas the family proof is given on paper. The companion
ScalarEightFifths.lean proves a smaller plateau including all genuine digit
multipliers end-to-end in Lean and uses no tabulated Roth numbers.
