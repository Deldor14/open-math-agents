# Growth at short rational dilations for progression-free sets

For fixed k ≥ 3 write R(n)=r_k(n) for the maximum size of a subset of [1,n]
containing no nonconstant k-term arithmetic progression. Put q=k−1 and let
T be the positive root of (q−1)T(T−1)=1.

**Theorem.** One can compute a rational λ strictly between 1 and T,
a positive rational ε and an integer N such that

    R(floor(λ n)) ≥ (1+ε) R(n) for every n ≥ N.

For k=3 the mixed-radix example below gives λ=F₁₁₂/F₁₁₁, ε=10⁻¹⁴²
and N=3·10²⁸⁴. Here F₀=0, F₁=1. This improves all three parameters
of our [earlier three-term estimate](../effective-growth/EffectiveGrowth.md).
For k=4 one example has λ<(1+√3)/2, ε=10⁻⁶⁶⁸ and N=10¹⁷⁶³.
The estimates hold on every sufficiently large scale. They do not identify
an asymptotic equivalent for R.

## Joining intervals

Suppose y≤g and z≤(k−2)g. Place optimal sets in [1,y] and
[y+g+1,y+g+z]. An increasing arithmetic progression of step d≤g cannot
cross the gap. For d>g, at most one term fits in the first interval
and at most k−2 in the second. Thus R(y+g+z)≥R(y)+R(z).
This and subadditivity hold also after multiplying all lengths by the same
integer t. The interval construction is checked on the upstream definition
of maxCard in LongGluing.lean.

## Propagating differences

Fix a positive integer t. Write P(j)=R(jt), D(a,b)=P(b)−P(a).
If x≤A, y≤g, A−x≤(q−1)g and y+g+A−x≤B, the interval construction
and subadditivity give

    P(y)+P(A−x) ≤ P(B),    P(A) ≤ P(x)+P(A−x).
    P(y)−P(x) ≤ D(A,B).

LongScaleSteps.lean proves this implication for maxCard itself.

Starting with a<b, put A=a+(q−1)b, B=a+qb+1 and U=B−A=b+1.
Write L=A−(q−1)U=a−(q−1), allowing a signed difference here. Starting
at x=a, take steps until x=b by the rule

    y = min(b, x+floor((x−L)/(q−1)), floor((U+x)/2)).

If x<b, then x−L≥q−1 and U≥x+2. Each step increases x. With
g=U−(y−x), the two bounds in the minimum give A−x≤(q−1)g and y≤g,
and y+g+A−x=B. Summation over the m steps gives D(a,b)≤m D(A,B).
Also P(A)≤qP(a)+(q−1)D(a,b).

Let (u₀,v₀)=(q,q+1) and iterate
(u',v')=(u+(q−1)v,u+qv). Its matrix has determinant one. The determinant
uᵢvᵢ₊₁−vᵢuᵢ₊₁ is one initially and stays one. Thus vᵢ/uᵢ increases.
Its update t↦(1+qt)/(1+(q−1)t) is strictly increasing and fixes T.
The initial ratio (q+1)/q is below T, as follows by substitution into
(q−1)t(t−1). All ratios are strictly below T.

For an integer s≥1 set K=vₛ₊₁, a₀=Kq−1, b₀=K(q+1).
Iterating (A,B) above gives aᵢ=Kuᵢ−1 and bᵢ=Kvᵢ. In particular
bₛ/aₛ=vₛ₊₁/uₛ₊₁ by the determinant identity. Put E₀=0 and
Eᵢ₊₁=(qEᵢ+q−1)mᵢ, where mᵢ is the number of steps on the i-th grid.
Induction using the two inequalities proves

    P(aₛ) ≤ qˢ P(a₀) + Eₛ D(aₛ,bₛ).

## An effective seed for every fixed k

Write Q=floor(uₛ/(2q)). Suppose [0,Q−1] contains a three-term-free set
of size C>qˢ. The low digits from this set and high digits from a k-term-free
subset of [0,a₀t−1] give

    C P(a₀) ≤ R((2Q−1)a₀t) ≤ P(aₛ).

Indeed low digits in a midpoint equation have second difference of absolute
value <2Q−1, hence their integer second difference vanishes. They are all
equal on every consecutive triple, after which the high digits would
give a k-term progression. The length inequality follows from 2qQ≤uₛ.
More generally a three-term-free digit set of span ≤(M−1)/2 may be used
directly at odd modulus M provided Ma₀≤aₛ. This finite product rule is
also [verified in Lean](../LocalGrowth.lean).

To see that the search terminates, the leading eigenvalue of the orbit matrix
is ρ=(q+1+√((q+1)²−4))/2>q. The other eigenvalue is 1/ρ. The recurrence
for u has a positive coefficient of ρˢ, since u₁>u₀>0.
Choose an alphabet size d≥2 with ρ^(log d/log(2d−1))>q. In base 2d−1,
all digit vectors of length h=floor(log Q/log(2d−1)) and entries 0,…,d−1
fit into [0,Q−1]. Some squared-norm layer has at least
dʰ/(1+h(d−1)²) elements. Each layer is three-term-free: digit second
differences cannot carry, and the Euclidean squared norm is strictly
convex on nonconstant segments. With this fixed d and s tending to infinity,
the lower bound is at least a positive constant times
(ρ^(log d/log(2d−1)))ˢ/(1+s), and eventually exceeds qˢ.
One can simply enumerate (s,d,h) and check the two integer inequalities
(2d−1)ʰ≤Q and dʰ>qˢ(1+h(d−1)²).

Substitution gives D(aₛ,bₛ)≥e P(aₛ), where e=(C−qˢ)/(CEₛ).
For general n≥aₛ, take t=floor(n/aₛ). Since R increases by at most one
per site, R(aₛt)≥R(n)−aₛ and R(floor(λn))≥R(bₛt) for λ=bₛ/aₛ.
Consequently (1+e)(R(n)−aₛ) is a lower bound. Also R(n)≥√(n/3):
binary digits 0,1 in base 3 give 2ʰ points when 3ʰ≤n<3ʰ⁺¹.
This absorbs the constant loss. For instance ε=e/2 works if
R(n)≥4aₛ/e since e≤1.

## Two integer certificates

For k=4 take s=184 and use 29 digits from 0 through 2047 in base 4095.
Take the ceiling of 2048²⁹/(1+29·2047²) as C. The modulus 4095²⁹ is
at most Q. The verifier checks the seed, the exact dilation, 262,353
admissible steps, e≥2·10⁻⁶⁶⁸ and 10¹⁷⁶³≥3(2aₛ·10⁶⁶⁸)².
The last two bounds give the constants of the theorem.

For k=3 take s=53. Use two digits of width 24 and eleven of width 26,
in the respective bases 47 and 51. The total modulus is M=47²·51¹¹.
Use vectors with sum of the digit charges ((2j−d+1)²−1)/8 equal to 348,
where 0≤j<d in each coordinate. They lie on one sphere after centering
and their mixed-radix encodings have span at most (M−1)/2.
Two independent integer coefficient calculations give C=9,436,763,481,513,984
points, exceeding 2⁵³. The 11,886 step inequalities give e≥2·10⁻¹⁴².

For this last example use the piecewise-linear interpolant r of R and take
t=n/aₛ. The rational-grid subadditivity and gluing for three terms are
proved in [eilamc14's interpolation file](https://github.com/eilamc14/open-math-agents/blob/d8ca5d4abbf28eb0af283e37f6b4c5f3162bf5ae/research/erdos142/DoublingGrowth.lean).
The same chain applies to r(jt). The check M(a₀+1)≤aₛ ensures that
M ceil(a₀t)≤n whenever t≥1, so the seed inequality still holds.
Rounding down λn costs at most one. Since n≥3·10²⁸⁴ gives R(n)≥10¹⁴²
and n≥aₛ, this proves the announced bound. This adapts the Fibonacci argument
of [the earlier Deldor14 growth note](https://github.com/Deldor14/open-math-agents/blob/89efc98c34189fc5b3916e52a2ed52d313c44744/research/erdos142-hinge/RothGrowth.md).

Run `python3 verify_long_growth.py` with assertions enabled.
The general propagation, seed existence and asymptotic conclusions are
written proofs. The interval gluing and its one-step application compile in
Lean 4.33.1 from the AP definitions pinned by the repository, with
propext, Classical.choice and Quot.sound. Compile LongGluing.lean after
LocalGrowth.lean and LongScaleSteps.lean after LongGluing.lean.
