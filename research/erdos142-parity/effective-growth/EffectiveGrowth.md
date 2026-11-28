# Effective growth of the finite Roth number below the golden ratio

Write R(n) for the largest size of a subset of {1,…,n} containing no
nonconstant three-term arithmetic progression, and Fᵢ for the Fibonacci
numbers with F₀=0 and F₁=1. We prove the following two statements.

1. For **every** nonnegative integer n, 127 R(5n) ≥ 128 R(3n).
2. Take λ=F₁₁₄/F₁₁₃. For **every** integer n ≥ 3·10²⁹⁰,
   R(⌊λn⌋) ≥ (1+10⁻¹⁴⁵) R(n).

Here λ is strictly smaller than the golden ratio and also smaller than
F₁₇₂/F₁₇₁ in the earlier [qualitative growth result](https://github.com/Deldor14/open-math-agents/blob/89efc98c34189fc5b3916e52a2ed52d313c44744/research/erdos142-hinge/RothGrowth.md).
The bounds apply independently of whether the density drops on that scale.
They give one-sided growth estimates. The ratio-one asymptotic equivalent
asked for in [Erdős problem 142](https://www.erdosproblems.com/142) remains undetermined.

## Interpolation and the 5/3 estimate

Let r(t) be the continuous piecewise linear interpolant of R at the
nonnegative integers. For nonnegative rational arguments u,v we use

    r(u+v) ≤ r(u)+r(v) ≤ r(u+v+max(u,v)).

The first inequality restricts an extremal set to two intervals.
For positive integer lengths u≥v, the second inequality already holds
at 2u+v−1 by leaving a gap between two optimal sets. That one-site saving
allows the inequalities to survive linear interpolation, as proved by
eilamc14 in [note #160694 and its Lean source](https://github.com/eilamc14/open-math-agents/blob/d8ca5d4abbf28eb0af283e37f6b4c5f3162bf5ae/research/erdos142/DoublingGrowth.lean).
The interpolant is nondecreasing.

The accompanying file ScaleSteps.lean gives a positive integer combination
of 26 instances of these inequalities. Applied to P(i)=r(it), it yields
128 P(144) ≤ 127 P(240). Take t=n/48 to obtain the first statement.
The Lean theorem refers directly to mathlib's rothNumberNat.

## Quantitative propagation

Fix a positive rational t and put P(j)=r(jt) on integer grid indices.
Write D(a,b)=P(b)−P(a). Suppose a≤x<y≤b≤A and

    y+(A−x)+max(y,A−x) ≤ B.

Adding the two interval inequalities gives P(y)−P(x) ≤ D(A,B):
indeed P(A) ≤ P(x)+P(A−x), whereas P(y)+P(A−x) ≤ P(B).
Thus any chain of k admissible steps from a to b gives
D(a,b) ≤ k D(A,B). The single-step implication is also verified in Lean.

Let s=54, K=F₁₁₄ and start at a₀=2K−1, b₀=3K. At each step set

    A=aᵢ+bᵢ,    B=aᵢ+2bᵢ+1,    (aᵢ₊₁,bᵢ₊₁)=(A,B).

In this step aᵢ=2A−B+1 and bᵢ=B−A−1. Starting at x=aᵢ, repeatedly take

    y=min(bᵢ, 2x−(2A−B), ⌊(B−A+x)/2⌋).

Whenever x<bᵢ, the new point is strictly larger. The second and third
terms in the minimum guarantee y+(A−x)+max(y,A−x)≤B. Denote the number
of steps by kᵢ. Besides the bound for D we have
P(A)≤P(aᵢ)+P(bᵢ)=2P(aᵢ)+D(aᵢ,bᵢ). With E₀=0 and
Eᵢ₊₁=(2Eᵢ+1)kᵢ, induction gives

    P(aₛ) ≤ 2ˢ P(a₀) + Eₛ D(aₛ,bₛ).

The supplied verifier checks every index, counts the steps using integers,
and computes Eₛ exactly. The endpoints are aₛ=K F₁₁₁−1 and bₛ=K F₁₁₂.
Their ratio reduces to F₁₁₄/F₁₁₃. These identities also follow by applying
the Fibonacci recurrence to the pair (aᵢ+1,bᵢ).

## A large set at the bottom scale

Put q=⌊(F₁₁₁−1)/4⌋. Use twelve digits 0,…,37 in base 75. All encoded
vectors lie in an interval of length (75¹²+1)/2 ≤ q. Choose the vectors with

    Σ ((2dᵢ−37)²−1)/8 = 702.

There are C=19,268,048,304,586,752 such vectors. The calculation is the
coefficient of degree 702 in (2 Σⱼ₌₀¹⁸ X^(j(j+1)/2))¹². The verifier
checks it both by integer convolution and by independent radix evaluation.
In a midpoint equation every digit second difference has absolute value
at most 74, so reducing modulo 75 and dividing successively gives a
midpoint equation in the digit vectors. All centered vectors have the
same squared norm. Strict convexity makes a midpoint trivial.
Thus R(q)≥C>2⁵⁴.

For positive integers q,m the carry-free digit construction places R(q)R(m)
points in [(2q−1)m]. Use a low digit in an optimal subset of [0,q−1]
and a high digit in an optimal subset of [0,m−1]. Any midpoint equation
first forces the low digits to coincide and then forces the high digits to
coincide. In particular R((2q−1)m)≥C R(m) for the value of q above.

Now take t=n/aₛ for an integer n≥aₛ, so t≥1. The certificate checks
(2q−1)(a₀+1)≤aₛ. Since ⌈a₀t⌉≤(a₀+1)t, the product construction with
m=⌈a₀t⌉ gives C P(a₀)≤R(n)=P(aₛ). Substitution in the propagation bound
shows

    r(λn)−R(n) ≥ ((C−2⁵⁴)/(C Eₛ)) R(n) > 2·10⁻¹⁴⁵ R(n).

Finally R increases by at most one per site. Also R(n)≥√(n/3) for n≥1:
take the 0/1 ternary digit vectors of length h with 3ʰ≤n<3ʰ⁺¹. They
are progression-free by the same digit argument and give 2ʰ≥√(3ʰ).
For n≥3·10²⁹⁰ we have n≥aₛ and R(n)≥10¹⁴⁵. Rounding λn down loses
at most one point, proving the second statement.

## Verification

Run `python3 verify_effective_growth.py` for the sphere, the path
certificate and the final constants. To compile ScaleSteps.lean, build
the linked DoublingGrowth.lean first in the same Lean 4.33.1
mathlib environment, placing its resulting module on LEAN_PATH.
The estimate at 5/3 is a full Lean theorem. The sub-golden-ratio estimate
is a written proof with exact integer checks and a Lean-verified local step.
