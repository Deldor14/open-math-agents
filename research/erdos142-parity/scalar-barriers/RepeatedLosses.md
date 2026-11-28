# Repeated density losses with the actual leading Roth deficit

Let R(n) denote the interval Roth number and let d(n)=log₂(n/R(n)). For every finite prefix length p there is an integer sequence H with H=R through p, H≥R everywhere, and

    0 ≤ log₂(H(n)/R(n)) ≪ₚ d(n)^(4/5) log(e+d(n))^(1/5).

It has all the properties of [the nonlinear model](SelfConsistentDigits.md), including subadditivity, unit increments, the one-site join, H(m)H(n)≤H((2m−1)n), the stated simultaneous affine rules and liminf H(⌊987n/610⌋)/H(n)=1. Yet **no regularly varying function of index one stays within a bounded factor of H on both sides**. In [the dyadic window criterion](RegularMajorants.md) this model has C=∞. The same error estimate and the same arithmetic requirements also admit a model with C=987/128.

When the actual dyadic deficit is bounded above and below by constant multiples of tᵅ for a fixed 0<α<1, the first model can still satisfy log₂(H(n)/R(n))=Oₚ(log(e+d(n))). Thus polynomial multiplicative precision in the deficit can coexist with the failure of every bounded-factor regularly varying approximation to the model. The unknown value of C for R is independent of these examples.

## A repeated finite portion of the scale schedule

Use the notation of [MatchedDeficit.md](MatchedDeficit.md). In particular ρ=128/987, c=log₂(1/ρ), e(t)=1+d(2ᵗ), and T is the largest t with e(t)≤y. The original cost of a positive step h is b(h)=T(c(h+1)+C₀)+C₁. For any nonnegative integer costs b, write S_b(i) for the maximum total cost over compositions of i, with S_b(0)=0.

Fix 0≤h<M. Give the single weight M the new cost K=S_b(M+h), keeping all other costs. Then

    S_new(M+s) = K+S_b(s)     for 0≤s≤h,       S_new(s)=S_b(s) for s<M.        (1)

A composition of M+s can use at most one M. With one M the remainder has cost at most S_b(s), and that bound is attained. Without M its cost is at most S_b(M+s)≤K. The new cost is at least the original one at M. The [Lean proof](BurstClock.lean) also allows any K≥S_b(M+h).

Take hₖ=k, and choose Mₖ successively very large with Mₖ₊₁>Mₖ+hₖ. At stage k use the previous finite collection of changes as b in (1). The final infinite list of costs stabilizes on every finite input. Let S be its composition maximum. It is superadditive, it retains all original lower separations, and

    S(Mₖ+s) = S(Mₖ)+S(s)      for 0≤s≤hₖ.                                    (2)

The equality follows at stage k from (1), and later changes have larger weight than Mₖ+hₖ. All properties in the nonlinear construction that use only superadditivity or a lower separation therefore still hold. The transition starting positions are Nᵢ=2^S(i).

## Preserving the quantitative comparison with R

Write E(i)=(1+i)^(4/5) log(e+i)^(1/5). With any finite list of cost changes the previous estimates give

    e(S_old(i)) ≤ ci + A E(i) + B_old.                                         (3)

Importantly the coefficient A can be fixed independently of that finite list. In the proof by dyadic groups of parts L≤h<2L, every group missing all the changed weights obeys the original bounds with the original constants. There are finitely many other groups. For each of those, its total cost at total weight s is ≤C_L s for a finite constant depending on the group. Since e(t)=O(1+√t), its positive excess over cs is bounded uniformly in s. The sum of these finite bounds is absorbed by B_old.

For the current choice h=k choose M sufficiently large that B_old≤E(M) and e(K)≤(c+1)M, using (3) at M+h with h fixed. In particular K≤T((c+1)M)≪M⁶ log(e+M). Additional lower requirements on M below are compatible with these two.

Consider an integer i for which M is the largest newly weighted index ≤i. Let q be the multiplicity of M in a maximizing composition. Its other parts use only the old costs. Two estimates are available.

* If e(qK)≤c qM and q≥1, combine this with (3) at i−qM to obtain e(S(i))≤ci+O(E(i)). The same conclusion follows directly from (3) when q=0.
* Expanding every copy of M into an old maximizing composition of M+h gives S(i)≤S_old(i+qh). If qh≤C E(i) for an absolute C, (3), B_old≤E(M) and i+qh≤2i again give e(S(i))≤ci+O(E(i)).

We show that at least one estimate always applies. The choice divides according to the inverse deficit of the given input R.

If liminf as y→∞ of T(y)/(y⁶ log(e+y)) is zero, choose M on an unbounded subsequence for which

    K ≤ T((c+1)M) ≤ M⁶ log(e+M) / h⁵.

Such integers exist by rounding y/(c+1) down and using monotonicity. Since e(t)≪1+√t, the first estimate applies whenever q≥C₁'(1+K/M²), with a fixed large C₁'. Otherwise q≪1+M⁴ log(e+M)/h⁵. Choose M large enough that the latter term is at least one. Then h q^(1/5)≪M^(4/5) log(e+M)^(1/5). As i≥qM, this implies qh≪E(i). The constants are independent of k.

In the other case T(y) is bounded below by a positive multiple of y⁶ log(e+y) for all sufficiently large y. Inverting this inequality gives e(t)≪1+(t/log(e+t))^(1/6). For example, take y to be a sufficiently large constant times (t/log(e+t))^(1/6), for which T(y)≥t. Hence e(qK)≪q^(1/6)M for all q≥1 and all chosen M sufficiently large: apply the increasing upper envelope at C qM⁶log(e+M), whose logarithm is at least a constant times log(e+M). The first estimate applies for all q above a fixed constant. For the remaining q choose M with h≤E(M), giving the second estimate. This establishes (3) with O(E(i)) uniformly for the infinite list.

The lower calibration e(S(i))≥ci−constant follows from the unchanged lower costs. The pointwise comparison with R now follows by the same sandwich of d(n) between consecutive levels when Nᵢ≤n<Nᵢ₊₁. The densities of the model in this range are within constant factors of ρⁱ.

Under the two-sided power hypothesis e(t)≍tᵅ, use E(i)=log(e+i) in (3). For unmodified groups this is the conditional estimate in MatchedDeficit.md. A fixed changed group still has bounded positive excess, now by e(C_L s)=O_L(1+sᵅ). The choice e(K)≤(c+1)M implies K≪M^(1/α). Therefore e(qK)≪qᵅM. For q above a fixed constant the first estimate applies, and for bounded q choose M large enough that h≤log(e+M). This proves the conditional assertion with the same construction, by imposing the stronger choices on M whenever the hypothesis holds.

## A single limit profile with unbounded density loss

For each fixed h≥1 and k≥h, (2) gives a dyadic window of exactly S(h) steps from N_(Mₖ) to N_(Mₖ+h). At both endpoints the unrounded model uses the respective incoming line. The ratio of the first to the last density tends to ρ^(−h) as k→∞, since the h successive slope factors κᵢ=ρ+(1−ρ)2⁻ⁱ tend to ρ. The integer rounding contributes a vanishing relative error. The window length S(h) is fixed before taking this limit. Sending h to infinity proves C=∞.

More precisely, the functions H(⌊x N_(Mₖ)⌋)/H(N_(Mₖ)) converge uniformly on each compact subinterval of [1,∞). Their limit starts at value one. Its successive transition starts are 2^S(s), s=0,1,…, with the original finite profile at zero tilt and incoming slope ρˢ. On a fixed compact interval, only finitely many transitions occur. Their starts and ends are eventually fixed after rescaling, by (2); each rescaled tilted profile converges uniformly to the untilted one and the rounding error is at most a constant divided by H(N_(Mₖ)). The density of the resulting limit function tends to zero as x→∞. This is compatible with the leading deficit of the original input R at all integers.

If a regularly varying W were within a bounded factor of H in both directions, a fixed multiple would majorize H eventually. The lower bound on the limsup from each of the dyadic windows would then exceed any fixed constant. This proves the claimed obstruction without assumptions on concavity of W. The asymptotic construction is a written proof. The replacement identity (1) and the underlying composition maximum have been checked in Lean.
