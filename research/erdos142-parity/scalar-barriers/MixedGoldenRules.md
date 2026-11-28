# Testing inequalities involving several interval lengths at the golden ratio

Let R(n) be the interval Roth number. Set φ=(1+√5)/2, Q=φ², and let F be the continuous profile of [GoldenRule.md](GoldenRule.md), normalized by F(1)=F(1/φ)=1. Its right inverse P reads binary expansions with weights Q instead of 2 and uses the terminating expansion at dyadic inputs. The original extremal profile is due to [eilamc14](https://github.com/eilamc14/open-math-agents/blob/512dda260bf02ae754b12997869c5f447a461d34/research/erdos142/GoldenRatioThreshold.md).

Consider any collection of positive linear inequalities at different lengths

    Σⱼ bⱼ f(aⱼx) ≤ f(Lx),                   aⱼ,L>0, bⱼ≥0.                  (1)

Each sum is finite. There is a nondecreasing continuous splitting and gluing profile with a normalized golden plateau satisfying all the rules if and only if, separately for each rule,

    Σⱼ bⱼ F(aⱼ/L) ≤ 1.                                                      (2)

In particular one evaluation per rule tests every scale, even if some aⱼ>L. For any such rules known for R with bounded additive changes in the integer arguments, a violation of (2) forces a uniform positive gain for R at some fixed dilation below φ, provided the rules hold eventually. This qualitative test applies to prospective constructions with different input lengths. The previously published [unequal-fibre construction](https://lefttosolve.com/api/desk/board?problem=Erdos142.erdos_142.variants.three&since=181116&limit=1) of pwamsley2015 gives particular rules for R with bounded additive changes.

## One test

Write C(y)=Σ bⱼ F(aⱼy/L), a nondecreasing continuous subadditive function with C(Qy)=2C(y). Every x satisfies Lx≤P(F(Lx)). For a sum t of distinct binary atoms d=2ᵏ, P(t)=Σ P(d) and P(d)=Qᵏ. Thus C(P(t))≤Σ C(Qᵏ)≤Σ2ᵏ=t under (2). Truncate any nonterminating binary expansion to get the same inequality by continuity of C and convergence of the two digit sums. This proves (1). Conversely take x=1/L for F. For any other normalized plateau profile the input and output at this test can all be scaled by the same Q⁻ᵏ into [0,1], where that profile is forced to agree with F. Its values there are precisely 2⁻ᵏ times the original test values. The compactness argument of GoldenRule.md proves the strict-gain consequence. For integer R, bounded changes in the arguments cost O(1) by its unit increments and disappear after normalization.

For a finite Fibonacci or geometric profile G with right inverse Pₛ, outgoing period 2ˢ in value and binary weights wₖ=Pₛ(2ᵏ), replace the single test by Σ bⱼG(aⱼwₖ/L)≤2ᵏ for 0≤k≤s. Here we assume Σ bⱼaⱼ≤L. For arbitrary t, Pₛ(t) is the sum of its atom capacities plus the ordinary fractional remainder v; atoms of size 2ˢ can repeat. The remainder costs at most v because G(y)≤y. The same proof now works without any limiting argument. The [Lean file](MixedProfileTest.lean) verifies the two criteria under their stated inverse and expansion hypotheses.

## Integer models with the same finite rules at every length

Suppose each rule in a fixed finite list has positive integers aⱼ,L, fixed integer offsets eⱼ,e₀, and nonnegative real bⱼ. Require all arguments to be nonnegative for integer n≥1. Assume

    Σⱼ bⱼ R(aⱼn+eⱼ) ≤ R(Ln+e₀)   (n≥1),              Δ=L−Σⱼ bⱼaⱼ>0.       (3)

Under these assumptions (2) for each rule is **necessary and sufficient** for the existence of a nondecreasing integer H with unit-bounded increments, splitting and the exact one-site join, satisfying all of (3) with H in place of R and

    H≥R,         H=R on any prescribed finite prefix,
    H/R≤g eventually for any prescribed g(n)→∞,        liminf H(⌈φn⌉)/H(n)=1.

Necessity follows by scaling H along its near-plateaus, as for R above. Here H(0)=0 and splitting gives the usual equicontinuity from gluing. The ingredients that give sufficiency follow. Strict linear slack Δ>0 is part of this theorem.

### Keeping the exact prefix in a mixed inequality

Put d(t)=log₂(2ᵗ/R(2ᵗ)). It is nondecreasing and o(t) by tiling and Behrend. For any fixed k there are arbitrarily late centers t with d(t+k)−d(t−k) arbitrarily small; otherwise disjoint intervals of 2k steps would give linear growth. Set u=2^(t−k), T=2ᵗ, v=2^(t+k), and δ_m=R(m)/m. Choose ε>0 sufficiently small for the finite list of strict slope margins. Take k large and one of these centers with δ_u≤2^ε δ_v. Set P₀=⌈1/((1−ε)δ_v)⌉. Roth's theorem allows δ_v to be as small as required.

For m≤T, tiling v by intervals of length m gives δ_m≥δ_v/(1+m/v)≥(1−ε)δ_v≥1/P₀. Thus B(m)=max(R(m),⌈m/P₀⌉) agrees with R through T. Fix A greater than twice the largest ratio of input multipliers within a rule and increase k so A2⁻ᵏ≤ε. For m≥T/A, tiling m from u gives δ_m≤(1+A2⁻ᵏ)δ_u≤(1+O(ε))/P₀. If any ceiling strictly beats R on one input, its length exceeds T, so every input of that rule exceeds T/A for T large, including all fixed offsets. Every B-input is then at most (1+O(ε))m/P₀+1. Since T/P₀ tends to infinity along these centers and n is bounded below by a fixed positive multiple of T, Δn/P₀ pays all rounding and offset costs after ε is chosen sufficiently small. The output is at least (Ln+e₀)/P₀. If no ceiling wins, use (3) directly. The one-site join and splitting for B are [already verified](FinitePrefix.md).

### Ending a finite profile after the plateau used for the model

Use the geometric weights Qⁱ up to depth s with M=2ˢ, width W=Qˢ and ρ=M/W. Write Uₛ for the profile truncated onto the line ρy at DW, D≥6, as in [GoldenIntegerModel.md](GoldenIntegerModel.md). It satisfies splitting and gluing, ρy≤Uₛ(y)≤ρy+M, Uₛ(y)≤y. Before W its values are at most F(y): the two capacity functions agree at all integer levels up to M, and the truncated fractional inverse dominates the geometric fractional inverse there.

Choose a fixed d≥0 such that Qᵈ≥max(1,maxⱼ aⱼ/L) for all rules. For Lx≤Q^(s−d) every finite atom needed to decompose Uₛ(Lx) has index k≤s−d. The costs at these atoms are bounded by ΣbⱼF(Qᵏaⱼ/L)≤2ᵏ, since their arguments are at most W. The atom and remainder proof then gives the mixed rule in this range. For Lx>Q^(s−d) its possible violation is at most MΣbⱼ, by the global upper and lower bounds on Uₛ. Choose a constant K>0 such that KΔ>2LQᵈΣbⱼ for each rule. For all large s let θ=Kρ≤1/2. The tilted profile Vₛ(y)=(1−θ)Uₛ(y)+θy has, in both ranges, surplus

    Vₛ(Lx)−Σⱼ bⱼ Vₛ(aⱼx) ≥ θΔx/2.

This choice matters when some inputs are longer than the output. For example F(1/2)=3/4 and F(3)=5/2, so the rule with L=2 and (a,b)=(1,1),(6,1/10) passes (2) with equality. The untilted geometric profile at s=3 has G₃(Q³/2)=6, G₃(3Q³)=24 and G₃(Q³)=8, and fails the rule. These numerical parameters illustrate the profile calculation only.

The plateau used in the splice is now at depth j=⌊s/2⌋, with endpoints 1+(Qʲ−1)/(Q−1) and Qʲ and height 2ʲ before tilting. The relative gain at dilation φ there is O(2⁻ʲ+K(2/Q)^(s−j)), tending to zero. This leaves enough room after that plateau to pay for every terminal discrepancy.

Choose sᵢ tending to infinity as slowly as prescribed with successive increases at most one. The outgoing slope of V at stage i is ρᵢ[1+K(1−ρᵢ)]. Consequently the actual logarithmic slope drop is sᵢ log₂(Q/2)−log₂[1+K(1−ρᵢ)], comparable to sᵢ uniformly after choosing a large initial depth. Use the actual cumulative drops in the first-crossing schedule of GoldenIntegerModel.md. Its logarithmic separations are ≫sᵢ² by the true dyadic deficit increment bound. The supports have logarithmic widths O(sᵢ). Thus the entire fixed-ratio interval containing all unshifted inputs and output of any single rule meets at most one support. On such an interval the positive surplus just proved, in the rescaled copy, dominates all fixed integer errors; the smallest n involved is at least a fixed multiple of the support start. With no support, the linear segment has surplus Δ times its value at n. The sizes of the later segments tend to infinity at their starts. The first support can be placed so late that if any shifted argument meets or passes it, every shifted argument is already beyond the finite range where B differs from its ceiling. Unit Lipschitz continuity of the unrounded splice pays the fixed shifts as well as the one-site shortening. All other bounds for the prefix and splice then apply, including H≥R and log₂(H/R)=O(1+sᵢ+sᵢ₊₁) on the i-th stage. Choosing depths sufficiently slowly supplies the requested g. The construction with exact integer offsets and the infinite schedule are written proofs.
