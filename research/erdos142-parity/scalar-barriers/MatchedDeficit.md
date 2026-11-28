# A scalar model matching the logarithmic density deficit of the actual Roth numbers

Let R(n) be the interval Roth number and set d(n)=log₂(n/R(n)) for n≥1. For every fixed integer p≥1 there is a sequence H of nonnegative integers with H=R on [0,p], H≥R everywhere, such that

    0 ≤ d(n) − log₂(n/H(n)) = Oₚ(d(n)^(4/5) log(e+d(n))^(1/5)).                    (1)

In particular log(n/H(n))/log(n/R(n)) tends to one, at all sufficiently large integers. Nevertheless

    liminf H(⌊987n/610⌋)/H(n) = 1.                                            (2)

H starts at zero, is nondecreasing, has increments zero or one, is subadditive, satisfies H(a)+H(b)≤H(a+2b−1) for 1≤a≤b, and satisfies every genuine interval digit inequality R(m)H(n)≤H((2m−1)n) for m,n≥1. The comparison in (1) matches the leading logarithmic deficit, including any oscillations of its exponent. The error in (1) is additive on the logarithmic scale; it can be unbounded. The conclusion about a plateau concerns H. The analogous growth question for R at 987/610 remains open in this work.

## The inverse of the dyadic deficit

Put e(t)=1+d(2ᵗ) for integer t≥0. It is nondecreasing because R(2u)≤2R(u), and its increments are at most one because R(2u)≥R(u). The no-carry product R(2uv)≥R(u)R(v) gives

    d(2^(s+t)) ≤ d(2^(s+t+1)) ≤ d(2ˢ)+d(2ᵗ)+1.

Thus e is subadditive. It tends to infinity by Roth's theorem. For real y≥1 let T(y) be the largest t with e(t)≤y. Then

    T(y+z) ≥ T(y)+T(z),           y−1 < e(T(y)) ≤ y.                          (3)

Indeed the sum of the two maximizing indices is admissible at y+z; the successor of T(y) is inadmissible and costs at most one. The Behrend estimate in mathlib and Theorem 1.4 of Raghavan's v3 preprint give absolute constants with

    e(t) ≪ 1+√t,                 T(y) ≪ (1+y)⁶ log(e+y).                  (4)

For the second inequality evaluate the lower bound e(t)≳(t/log(e+t))^(1/6) at t=⌈C(1+y)⁶log(e+y)⌉. For sufficiently large absolute C it exceeds y, uniformly for y≥1. For arbitrary n, the difference between d(n) and d(2^⌊log₂ n⌋) is at most one by monotonicity and R(2u)≤2R(u). [Raghavan, Theorem 1.4](https://arxiv.org/html/2603.27045v3#S1) · [Behrend in mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Additive/AP/Three/Behrend.html)

The earlier version used the weaker denominator log(e+t) in the lower bound for e. Using the precise exponent 1/6 on that denominator improves the power of the logarithm in (1) from 6/5 to 1/5. If the stronger estimate T(y)≪(1+y)⁶ asserted in the [upper-bound manuscript by zeemy23](https://github.com/zeemy23/open-math-agents/blob/57a4b39e3fcfaf131dbe2d00aeae480da0889014/research/erdos142/upper-bound/UpperBound.md) is confirmed, the same argument omits the logarithmic factor altogether. The unconditional comparison here uses Raghavan’s stated theorem.

## Placing the transitions

Use the finite profile of [the recurrent construction](RecurrentProfiles.md), with incoming slope one, outgoing slope ρ=128/987, and transition support [1,W] with W=620·987. Write c=log₂(1/ρ). Near-plateaus occur on [610,987]. Exactly as in that construction let θᵢ=2⁻ⁱ. Only the transition locations change.

Fix two sufficiently large positive constants C₀,C₁ with C₁ an integer. Give a jump of h≥1 indices the integral cost

    b(h)=T(c(h+1)+C₀)+C₁.

Let S(0)=0 and let S(i) be the maximum of Σ b(hⱼ) over all compositions of i into positive integers hⱼ. This is a maximum over finitely many lists. Concatenation gives S(j+h)≥S(j)+S(h)≥S(j)+b(h) for h≥1. The maximizing list also shows that S is the smallest possible clock with S(0)=0 and these jump inequalities. Take Nᵢ=2^S(i). We have S(i)≥i b(1), so C₁ can pay any fixed minimum spacing and the rounding costs of the construction. We also have S(i)≥b(i).

We now show, for every i≥2, that

    ci+c+C₀−1 < e(S(i)) ≤ ci + O(i^(4/5) log(e+i)^(1/5)).                   (5)

The lower bound follows from S(i)≥T(c(i+1)+C₀) and (3). For the upper bound take a maximizing composition and group its parts by L≤h<2L, for L=1,2,4,… . Within a nonempty group write s for the sum of its parts and w for the sum of their costs. By (3), subadditivity and the definition of b, we have e(b(h))≤ch+C₂ with fixed C₂=c+C₀+e(C₁). The group has at most s/L parts, hence

    e(w) ≤ cs+C₂s/L.

Independently, (4) gives b(h)≪L⁶log(e+L), so w≪sL⁵log(e+L) and e(w)≪1+√(sL⁵log(e+L)). Thus e(w)≤cs whenever s is at least a sufficiently large constant times L⁵log(e+L). For lower s the previous linear estimate bounds the excess by O(L⁴log(e+L)). In all cases the positive excess is

    (e(w)−cs)₊ ≪ min(i/L, L⁴ log(e+L)).

Sum over dyadic L and use subadditivity of e across nonempty groups. For L≤i^(1/5)/log(e+i)^(1/5) sum the second bound as a geometric series, bounding its logarithm by log(e+i); for larger L sum the first. Their sum is O(i^(4/5)log(e+i)^(1/5)), proving (5) (with finitely many small i absorbed in the constant).

## Checking the integer model

Use the profile construction and rounding of [RecurrentProfiles.md](RecurrentProfiles.md) and the finite initial extension from [FinitePrefix.md](FinitePrefix.md). For clarity, Bₚ(n)=max(R(n),⌈n/p⌉) agrees with ⌈n/p⌉ for n>S₀, for a fixed S₀≥4p. Use Bₚ before N₁ and H(n)=⌈f(n)/p⌉ thereafter. For Nᵢ≤x<Nᵢ₊₁, f(x)≥ρⁱx. The incoming slopes αᵢ₋₁ are within fixed factors of ρⁱ⁻¹. The single-transition estimates, unit-increment bound, subadditivity and one-site gluing in those two proofs require only a sufficiently large first scale, sufficiently large consecutive ratios Nᵢ₊₁/Nᵢ, and sufficiently large products αᵢ₋₁θᵢNᵢ (and αᵢ₋₁θᵢNᵢ₋₁ for i≥2). They follow from S(i)≥i b(1) and S(i+1)−S(i)≥b(1), by choosing C₁ large compared to c+1 and the finite initial constants. We verify the two remaining digit cases, which previously used a different schedule.

If [n,(2m−1)n] meets k≥2 transitions beginning with j, then m≥Nⱼ₊ₖ₋₁/(2WNⱼ). Choose C₁≥⌈log₂(2W)⌉+2 and C₀≥5. The separation S(j+k−1)−S(j)≥b(k−1) implies that the integer ⌊log₂ m⌋ is at least T(ck+C₀). By (3) and the one-bit comparison for general m, d(m)≥ck+1. Thus ρᵏ(2m−1)≥2R(m). Between the two endpoints, the ratio of the lesser bound on the outgoing density to the greater bound on the incoming density is at least ρᵏ, so the factor two pays for rounding the digit inequality when n>S₀, because f(n)/p≥1.

If n≤S₀ but (2m−1)n reaches a scale Nᵢ, then ⌊log₂ m⌋≥S(i)−⌈log₂(2S₀)⌉. The dyadic one-bit increments, (3) and S(i)≥b(i) give d(m)≥ci+log₂ p, uniformly in i by taking C₀,C₁ large. As H(n)≤n and f((2m−1)n)≥ρⁱ(2m−1)n for the last transition index i, this pays the digit inequality for bounded inputs too. The same estimate with n≥Nᵢ in place of m gives d(n)≥ci+log₂ p, so H majorizes R on the tail. The finite prefix construction already gives this before N₁. The near-plateau ratio (2) follows by taking n=610Nᵢ since αᵢ₋₁Nᵢ/p tends to infinity.

## Comparing the deficits point by point

For Nᵢ≤n<Nᵢ₊₁ let t=⌊log₂ n⌋. Sandwich e(t) between e(S(i)) and e(S(i+1)). By (5) and the one-bit comparison, d(n)=ci+O(i^(4/5) log(e+i)^(1/5)). At the same n the model has log₂(n/H(n))=ci+Oₚ(1), by its bounds on the density and rounding. In particular i is comparable to d(n), and subtraction proves (1).

## How often a fixed dilation can have small growth

For any fixed 1<λ<987/610 and 0<ε<λ−1, this model also satisfies

    Σ_{1≤n≤X, H(⌊λn⌋)≤(1+ε)H(n)} 1/n  ≍_{λ,ε,p} d(X).

Indeed each complete transition contributes at least log(987/(610λ))+o(1) in harmonic weight. For 610Nᵢ≤n≤987Nᵢ/λ both arguments lie on the same constant portion of the untilted profile. The ratio for the tilted, rounded model tends to one uniformly there. Outside the intervals [Nᵢ/λ, WNᵢ+2] the two inputs are on one linear segment, and their ratio tends uniformly to λ since f(n)/p tends to infinity. The harmonic weight of each of the displayed transition intervals is bounded independently of i. Their number up to X, allowing either incomplete end interval, is d(X)/c+o(d(X)) by (5); natural logarithms in harmonic sums introduce no change to the claimed order.

This order is also an upper bound for the exceptional harmonic mass of the true R. More generally let F be positive, nondecreasing, subadditive on positive integers and write D_F(n)=log₂(n/F(n)). For n in [2ʲ,2ʲ⁺¹) choose a=2^(j−h), b=2^(j+h), m=⌊λn⌋, where the fixed h is large in terms of λ and ε. When F(m)≤(1+ε)F(n), tiling by intervals gives

    F(b)/b ≤ (1+m/b)(1+a/n)(1+ε)(n/m) F(a)/a.

The factor is at most a fixed q<1 for large n and h, since (1+ε)/λ<1. Thus D_F(b)−D_F(a)≥log₂(1/q) for every occupied dyadic bin beyond a fixed initial range. Dyadic increments are nonnegative by subadditivity and at most one by monotonicity. Summing the differences up to the bin of X uses each increment at most 2h times, including at most h bounded endpoint increments beyond X. Each dyadic bin has bounded harmonic mass. This proves the upper bound O(1+D_F(X)−D_F(1)). Combined with (1), our example attains this order while matching the actual leading density deficit. The genuine R might have fewer exceptional lengths. [Earlier quantitative regularity estimates](../README.md)

## Conditional precision

If for some 0<α<1 the actual dyadic deficit satisfies e(t)≍t^α for t≥1, the same construction gives

    0 ≤ log₂(H(n)/R(n)) = Oₚ(log(e+d(n))).

Indeed T(y)≪y^(1/α), and for a nonempty group in the preceding proof, e(w)≪s^α L^(1−α). As soon as s≥C L this is at most cs. Otherwise the excess is at most C₂s/L=O(1). There are only O(log i) nonempty groups. This conditional comparison allows a fixed power of the actual deficit as a multiplicative error on cardinalities. It requires two-sided constant bounds on the density deficit at the displayed power.

A weaker hypothesis, e(t)=t^(α+o(1)), already makes the additive error in the log comparison Oₚ,ε(d(n)^ε) for every ε>0. Fix δ>0 with 0<α−δ<α+δ<1. In a dyadic group we have e(w)≪(sL^(1/(α−δ)−1))^(α+δ). Its positive excess can occur only for s≪L^κ, where κ=(1/(α−δ)−1)(α+δ)/(1−α−δ)>1. Per group the excess is therefore O(min(i/L,L^(κ−1))). The dyadic sum is O(i^(1−1/κ)); since κ tends to one with δ, this yields the assertion. These two refinements use hypotheses on R. The leading equivalence and error (1) use the published unconditional bounds.

## Verification

[DeficitInverse.lean](DeficitInverse.lean) proves the dyadic monotonicity, one-step bound, subadditivity after adding log 2, divergence for the true mathlib Roth number, and both facts in (3). It uses natural logarithms, which amounts to multiplication of all the deficit levels and the one-step bound by log 2. [CompositionClock.lean](CompositionClock.lean) proves attainment of the maximum over compositions, superadditivity, every separation at once, and minimality. A [separate construction](DeficitSharpness.md) shows that both exponents in (5) are required by this separation criterion for abstract deficits obeying the same two growth envelopes. Sharpness for the actual Roth deficit is open. The analytic comparisons and the passage to the asymptotic conclusions are written proofs. This result restricts what can be deduced from the listed scalar inequalities together with leading logarithmic density information, even with an arbitrary exact finite prefix.

[The nonlinear digit extension](SelfConsistentDigits.md) constructs the same example with H on both product factors, the finite increment constraint and simultaneous affine digit rules. The [power-regime sharpness example](DeficitSharpness.md#two-sided-power-estimates) attains the conditional logarithmic error for abstract separation schedules.
