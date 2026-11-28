# Signed differences between several dilations of the true Roth number

Let R(n) be the largest size of a subset of [1,n] containing no nonconstant three-term arithmetic progression. All logarithms below are natural. Write

    H(t)=(1+t)^(5/6) log(e+t)^(1/6).

Fix positive real dilations aᵢ, real coefficients cᵢ and integer offsets eᵢ. Group equal dilations in the polynomial P(z)=Σ cᵢ aᵢᶻ and assume P is not identically zero. Let h be the order of its zero at 1, taking h=0 if P(1)≠0. Write σ for the sign of (−1)ʰP⁽ʰ⁾(1). Then

    limsup as n→∞ of H(log n)ʰ σ Σᵢ cᵢ R(⌊aᵢn⌋+eᵢ) / R(n) > 0.              (1)

Only sufficiently large n are used. In particular the signed sum in the indicated direction exceeds nᵝ infinitely often for every fixed β<1. As an explicit case, at infinitely many powers of two n,

    R(n)−R(2n)+R(4n)/4 ≥ c R(n)/[(log n)^(5/3) (log log n)^(1/3)]

for an absolute c>0. More generally for every fixed h≥1 and integer base b≥2 the h-th forward difference with alternating signs of R(n)/n is positive by the corresponding relative amount at infinitely many n along every chain n=n₀ bᵏ, for each fixed positive integer n₀. The powers of b in this assertion are input dilations; the difference is taken in the index k. Nothing in (1) supplies an asymptotic equivalent of R.

## The two input bounds

Set u(t)=e⁻ᵗ R(⌊eᵗ⌋) for t≥0 and zero for t<0. For all sufficiently large t, Behrend and Theorem 1.4 of Raghavan's v3 preprint give

    exp(−C√t) ≤ u(t) ≤ C exp(−c(t/log(e+t))^(1/6)).

Replacing eᵗ by its floor changes only the constants. The proof uses these two bounds and the fact that changing an integer input of R by one costs at most one. [Behrend's construction](https://doi.org/10.1073/pnas.32.12.331) · [Raghavan, §1](https://arxiv.org/html/2603.27045v3#S1)

For real m≥0 let Mₘ=∫₀^∞ tᵐu(t)dt. For positive integers m large,

    c m² ≤ Mₘ^(1/m) ≤ C m⁶ log(e+m).                                        (2)

For the lower bound integrate from m² to 2m². For the upper bound put g(t)=(t/log(e+t))^(1/6). The condition g(t)≤y gives t≤C(1+y)⁶log(e+y). Write exp(−cg(t)) as the integral of c exp(−cy) over y≥g(t), and integrate in t first. This bounds Mₘ by

    C^(m+2)/(m+1) · ∫₀^∞ e^(−cy) (1+y)^(6m+6) log(e+y)^(m+1) dy.

For A≥4/c, use log(e+y)≤log(e+A(m+1))(1+y/(A(m+1))). Raising the last factor to m+1 costs at most exp(cy/4). The remaining exponential moment of (1+y)^(6m+6) is at most (C'(m+1))^(6m+6), by integration of the gamma density. Taking m-th roots proves (2).

Moment ratios qₘ=Mₘ/Mₘ₋₁ are nondecreasing by log-convexity. There are infinitely many m with qₘ≤C₁m⁶log(e+m), with fixed C₁. Otherwise multiply the contrary lower bounds for all sufficiently large indices. The sixth power of m! contributes a constant times m⁶ after taking m-th roots, and the product of log(e+j) contributes at least a constant times log(e+m) after taking m-th roots (use j≥√m). Taking C₁ large contradicts (2).

## Testing the first nonzero signed moment

Put sᵢ=log aᵢ, wᵢ=cᵢaᵢ and Sⱼ=Σwᵢsᵢʲ=P⁽ʲ⁾(1). After grouping equal dilations, a Vandermonde matrix shows h is finite and is less than the number of distinct dilations with nonzero combined coefficient. Define V(t)=Σ wᵢu(t+sᵢ) and

    Iₘ=∫ℝ tᵐ V(t)dt = ∫₀^∞ [Σᵢ wᵢ(t−sᵢ)ᵐ] u(t)dt.

For fixed h and m→∞, the binomial theorem and S₀=⋯=Sₕ₋₁=0 give

    Iₘ = ((−1)ʰ Sₕ/h! + o(1)) mʰ Mₘ₋ₕ.                                    (3)

In detail, on t≥m^(3/2) the first surviving term is binom(m,h)(−1)ʰSₕt^(m−h). The sum of the higher terms is O(m^(−1/2)mʰt^(m−h)), by bounding each binomial coefficient by mʲ/j! and summing at m max|sᵢ|/t=O(m^(−1/2)). On the complementary interval the integral of the polynomial and leading term in absolute value is at most a fixed polynomial in m times (m^(3/2)+1+max|sᵢ|)^(m+1). This is o(mʰMₘ₋ₕ) by the lower bound in (2). The [Lean certificate](SignedScaleMoments.lean) checks the exact cancellation identity at every m≥h, its specialization to m=h, and the order-two stencil.

Along the subsequence of small qₘ,

    ∫₀^∞ tᵐ u(t) H(t)^(−h) dt ≤ Cₕ mʰ Mₘ₋ₕ.                                (4)

The contribution below m^(3/2) is negligible by the same lower bound. Above that point the integral is at most (log m)^(−h/6) M_(m−h+h/6). Log-convexity bounds the last moment by Mₘ₋ₕ qₘ^(h/6), also for nonintegral h/6. Substitution yields (4).

If σV(t)≤ε u(t)/H(t)ʰ at all sufficiently large t, integration gives σIₘ≤(Cₕε+o(1))mʰ Mₘ₋ₕ on that subsequence. The omitted interval, including the part below zero, is bounded independently of m in length and contributes at most C₀^(m+1). Choosing ε<|Sₕ|/(2h! Cₕ) contradicts (3). This proves the positive limsup for the continuous shifts. For n=⌊eᵗ⌋ we have eᵗV(t)=Σ cᵢR(⌊aᵢeᵗ⌋), and using ⌊aᵢn⌋+eᵢ changes that sum by O(1). Behrend gives H(log n)ʰ/R(n)→0, proving (1).

For lattice shifts replace u(t) by uₖ=R(n₀bᵏ)/(n₀bᵏ) on nonnegative integer k, zero below. With shifts sᵢ now integral, use sums Σₖ kᵐuₖ instead of integrals. Both estimates (2) hold with constants depending on b and n₀: the lower interval contains at least m² integers, and the sum up to T of kᵐ is bounded by (T+1)^(m+1), sufficient in the same upper-bound argument. The polynomial identity and all remaining estimates pass over without change. For the h-th difference take coefficients (−1)ʲbinom(h,j) directly on uₖ₊ⱼ. The first h−1 moments and the zeroth vanish, with the h-th moment equal to (−1)ʰh! by the ordinary binomial finite-difference identity.

## Scope of the obstruction

Every nondegenerate signed rule ΣcᵢR(⌊aᵢn⌋+eᵢ)≥0 holding eventually must have P(1−ε)>0 for all sufficiently small ε>0. In particular for a balanced mixed rule R(Ln+e₀)≥Σ bⱼR(aⱼn+eⱼ) with bⱼ≥0 and Σ bⱼaⱼ=L, set pⱼ=bⱼaⱼ/L. If some aⱼ≠L has positive weight, one must have

    Σⱼ pⱼ log(aⱼ/L)>0.

Indeed a negative mean gives the wrong first sign. A zero mean would make the second moment about log L equal to minus L times a strictly positive variance, giving the wrong second sign. This necessary condition tests a proposed rule without any search for finite extremal sets. It does not apply when the grouped polynomial vanishes identically, as can happen in a rule involving just bounded translations.

For any fixed 0<γ<1 the count model ⌈n exp(−(log n)ᵞ)⌉ eventually satisfies *every individual signed rule with the required leading sign*, whatever the value of γ. For a finite list it does so simultaneously beyond one threshold. To see this, write v(t)=exp(−tᵞ); for fixed j one has v⁽ʲ⁾(t)/v(t)∼(−γt^(γ−1))ʲ. Taylor expansion at the bounded shifts sᵢ leaves exactly the first nonzero signed moment at leading order. Integer roundings and fixed offsets cost O(1), absorbed because n v(log n) times any fixed inverse power of log n tends to infinity. Thus any finite list of eventually valid signed dilation rules of this nondegenerate kind, even with negative coefficients and cancellations of high order, is compatible with every deficit exponent strictly between 1/6 and 1/2. This assertion concerns the rules and the two bounding envelopes. It does not assert exact agreement on a prescribed prefix.

The scale H in (1) is sharp from the two input estimates. Take v(t)=exp(−(t/log(e+t))^(1/6)) and use the integer model ⌈n v(log n)⌉. The normalized expression on the left of (1) actually converges to |Sₕ|/(6ʰh!). Indeed for g=−log v, H(t)g'(t)→1/6 and g⁽ʲ⁾(t)=O(g(t)/tʲ) for each fixed positive j. In v⁽ʲ⁾/v the term (−g')ʲ dominates products with fewer than j factors since g(t)→∞. Taylor expansion at fixed shifts, including its next-order remainder, gives the asserted limit. No optimality for the actual R is inferred from this example. The moment estimates and the conclusions about R are written proofs.
