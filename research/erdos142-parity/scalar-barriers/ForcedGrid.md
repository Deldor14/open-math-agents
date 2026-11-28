# Rigidity of Fibonacci plateaus and a smaller dilation for the Roth number

Write R(n) for the finite Roth number and Fⱼ for the j-th Fibonacci number,
starting with F₀=0, F₁=1. An interval of equality in a scalar scaling profile
forces its value on an entire integer grid. Exploiting the room up to the
right endpoint gives the following positive result about the actual R:

    R(floor(λn)) ≥ (1+10^(-134))R(n) whenever n ≥ 3·10^268,

where

    λ = 747230980351474411985551361801500529348765790
        / 461814143304116035103818818074847139530008111
      < F₁₀₄/F₁₀₃ < F₁₁₂/F₁₁₁ < (1+√5)/2.

The gain 10⁻¹³⁴ and the starting threshold also improve
[the earlier three-term certificate](../long-growth/LongGrowth.md).
The changes in the dilation are very small. These bounds concern uniform
one-sided growth and leave the asymptotic equivalent undetermined.

## What a plateau forces

Suppose f is continuous, nondecreasing and nonnegative on the nonnegative
reals, f(0)=0, and f(x+y)≤f(x)+f(y)≤f(x+y+max(x,y)).
If f(a+b)=f(a+2b) for 0<a≤b, then

    f(x)=f(a+b)/2     for all a≤x≤b.

In fact f(x)+f(a+b−x)=f(a+b) throughout [a,b], by the two scalar
inequalities. If x is interior and y>x sufficiently close to x, then
y+a+b−x+max(y,a+b−x)≤a+2b. Consequently f(y)≤f(x). The same estimate
on every compact interval of interior points, in finitely many steps,
makes f constant throughout the interior. Continuity gives the endpoints.
For a=b both scalar inequalities give the conclusion immediately.
[Complete Lean proof](PlateauRigidity.lean).

Set wᵢ=F₂ᵢ₊₂, M=2ˢ and W=wₛ. If f(F₂ₛ₊₁)=f(F₂ₛ₊₂), apply this halving
argument recursively, because consecutive endpoint pairs have the form
(a+b,a+2b). It follows that f(wᵢ)=2ⁱ f(1) for 0≤i≤s and
f(F₂ₛ₊₁)=2ˢ f(1).

For 0≤j<M let A(j) be the sum of the wᵢ corresponding to set bits of j,
and let A(M)=W. The list of s binary weights plus an additional weight 1
has total length F₂ₛ₊₁, and the sum of its individual f-values is
M f(1), precisely f of its total length. In a tight subadditive decomposition
every subcollection is itself tight: split off the complementary collection
and use subadditivity. [Finite Lean lemma](CapacitySaturation.lean).
Choosing whether to include the additional weight 1 gives

    f(A(j)) = j f(1),       f(A(j)+1) = (j+1) f(1).

Thus for *each* integer 1≤n≤W,

    f(n) = min{j : A(j)≥n} f(1).

Indeed between A(j)+1 and A(j+1) the two forced endpoint values agree.
This identifies the values in the [binary countermodel](FibonacciBarrier.md)
as necessary at every integer through W for any continuous scalar profile
with that plateau. The claim does not prescribe the behavior inside the
unit-length increasing segments.

## A twelve-dimensional seed

Use three digits of width 30 (base 59) and nine of width 31 (base 61).
Both widths use the same half-integer center 29/2, including the odd width.
For each digit 0≤j<d put e(j)=((2j−29)²−1)/8. Select vectors whose
total charge is 459. There are exactly C=2,303,115,151,489,024, exceeding
2⁵¹. Their encodings have span at most (m−1)/2 with
m=59³·61⁹=2,401,732,030,400,183,044,439. Every midpoint equality
can be read digit by digit, and strict convexity on the common sphere
forces the vectors to coincide. They are also midpoint-free modulo m.
Hence for every integer u≥1 the digit product bound gives R(mu)≥C R(u).
For s=51, m≤F₁₀₄. The predicted plateau already contradicts the bound
at the pair 1,m whenever f(1)>0 and f(mx)≥Cf(x).

## An effective estimate for all sufficiently large n

To have a numerical threshold and gain, use the continuous linear interpolant
r(t) of the integer Roth numbers. Its subadditivity and gluing for rational
arguments follow from [eilamc14's Lean interpolation theorem](https://github.com/eilamc14/open-math-agents/blob/d8ca5d4abbf28eb0af283e37f6b4c5f3162bf5ae/research/erdos142/DoublingGrowth.lean).
Take s=51, u=F₁₀₃, v=F₁₀₄, d=2v, K=64d, and begin the integer recurrence
at (a₀,b₀)=(K−1,K−d). Replace (a,b) by (A,B)=(a+b,a+2b+1)
at each stage. Initially b₀<a₀, so subadditivity yields P(a₁)≤2P(a₀)
for P(j)=r(jt) with positive rational t. From stage 1 on we have a<b.

For these subsequent stages use the verified chain in
[the growth proof](../long-growth/LongGrowth.md), with q=2. Starting at
x=a take y=min(b,2x−(2A−B),floor((B−A+x)/2)) until b. Each step gives
P(y)−P(x)≤P(B)−P(A). If mᵢ is the number of comparisons let E₁=0,
Eᵢ₊₁=(2Eᵢ+1)mᵢ. Induction gives

    P(aₛ) ≤ 2ˢ P(a₀)+Eₛ(P(bₛ)−P(aₛ)).

The determinant check gives aₛv−bₛu=d−v>0. The larger seed can be
charged to the *right* endpoint: the verifier checks m(a₀+1)≤bₛ.
Take t=n/aₛ for integer n≥aₛ. Since m ceil(a₀t)≤bₛt, one has
C P(a₀)≤P(bₛ). Combining the two bounds gives

    P(bₛ)−P(aₛ) ≥ ((C−2ˢ)/(CEₛ+2ˢ)) P(aₛ).

The exact rational factor is at least 2·10⁻¹³⁴. The ratio bₛ/aₛ is
the λ above. Rounding down λn costs at most one. The elementary ternary
digit bound gives R(n)≥√(n/3) and 3·10²⁶⁸≥aₛ, proving the stated result.

Run `python3 verify_rigid_seed.py` for two independent coefficient
computations, 11,147 interval comparisons and the final integer checks.
The halving lemma and tight-subcollection lemma compile in Lean 4.33.1.
The grid classification and numerical growth theorem are written proofs
with the indicated local formalizations. No general solution is claimed.
