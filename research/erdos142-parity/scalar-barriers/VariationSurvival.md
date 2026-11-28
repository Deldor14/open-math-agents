# The total variation needed to retain points in the interval branching experiment

Let k≥3 be fixed. Put R(m)=r_k(m), the largest size of a subset of [0,m) avoiding nonconstant k-term arithmetic progressions. For 0≤f≤1 on [0,1], extended by zero off this interval, put

    L_f(x)= Σ_(j=0)^(k−1) ∫_(h>0) ∏_(i≠j) f(x+(i−j)h) dh,
    S_d(f)= ∫₀¹ f(x) exp(−d L_f(x)) dx.

The variational problem has a direct probabilistic meaning. At a root of continuous interval type x, potential incident progression edges through role j and positive spacing h have Poisson intensity d dh whenever all their sites lie in [0,1]. Independently accept a vertex of type u with probability f(u). Keep an accepted root only if it belongs to no fully accepted edge. Its unconditional survival probability is S_d(f). For k=3 this is the spatial, one-round version of the [local recovery problem](IntervalLocalRecovery.md).

For real d≥1, V≥1, let S(d,V) be the supremum over f of total variation at most V. Use the variation of a bounded-variation representative on the interval; changing endpoints or extending by zero costs at most two and has no effect on the constants. Define m as the largest integer 1≤m≤d satisfying

    R(m)(m/d)^(1/(k−1)) ≤ V.

Such an m exists. Then, with constants depending only on k,

    S(d,V) ≍ (m/d)^(1/(k−1)) R(m)/m.                                      (1)

There is no choice of regularity scale hidden in this comparison. The transition scale is set jointly by the available variation and the true number of free points at a shorter length. For unrestricted measurable f the supremum is ≍R(⌈d⌉)/⌈d⌉. To obtain any fixed positive fraction of this optimum, variation Ω(R(⌈d⌉)) is necessary, and variation O(R(⌈d⌉)) suffices.

This survival problem has a cap on pointwise probability and an absolute variation budget. The companion [circle-energy theorem](https://github.com/Deldor14/open-math-agents/blob/ba5689bbcc5751fbbee575f6cd50f7b4d9f75950/research/erdos142-hinge/RothCircleEnergy.md) studies unit-mass amplitudes, an integrated correlation plus its diagonal moment, and a relative Lᵏ derivative constraint. Those hypotheses and the resulting transition scale differ. The affine sampling below uses the classical Varnavides argument. [Croot and Sisask](https://ecroot.math.gatech.edu/prob-almost-periods.pdf)

## Unrestricted survival by finite affine sampling

On the circle of circumference two extend f by zero outside [0,1]; use Haar probability. Up to a null set, progressions supported in the interval lift to true real ones: their successive differences are in [−1,1] and congruent modulo two, with any ambiguity confined to the endpoints. For g=f exp(−d L_f), extended by zero too, let Λ(g) be the integral over a Haar-uniform first site and spacing of the product of the k values of g. The positive and negative spacings give the factor 2/2². By the arithmetic-geometric mean inequality applied to the k exponential factors,

    Λ(g) ≤ (1/(2k)) ∫ f(x) L_f(x) exp(−k d L_f(x)) dx
         ≤ S_d(f)/[2k(k−1)e d].

The first inequality uses the change of variables making the j-th site the root for each of the k terms. In the second, t exp(−(k−1)dt)≤1/[(k−1)e d].

Take b=⌈d⌉ and a random affine grid of b points on this circle, with independent Haar-uniform starting point and spacing. Independently select the indices with probabilities g at their images. The expected selected count is b S_d(f)/2. Each positive-step index progression is selected with probability Λ(g), since any positive integer multiple of the random spacing is Haar uniform. There are at most b(b−1)/[2(k−1)] index progressions by summing over the first site. Deleting at most one index per selected progression leaves at most R(b) points. Since b−1≤d, rearranging gives the unrestricted estimate

    S_d(f) ≤ 2 [1−1/(2e k(k−1)²)]^(−1) R(b)/b.                           (2)

The calculation works for all measurable profiles 0≤f≤1; it uses no container estimate. At 0<d<1 the bound S_d(f)≤1 suffices. The construction below at m=⌊d⌋ proves the reverse estimate in order of magnitude.

## Decomposing the amplitude and summing the layers

For a dyadic a=2^(−j−1), consider a<f≤2a. On this layer L_f≥a^(k−1)L_g where g is the indicator of {f>a}; this one-sided comparison uses nonnegativity also at the other sites of an edge. By the unrestricted estimate its contribution to survival is at most C_k a R(⌈d a^(k−1)⌉)/⌈d a^(k−1)⌉, also at arguments smaller than one by the trivial bound a.

There is a second upper bound C_k V/(d a^(k−1)). Indeed the layer can be covered up to null sets by at most 1+O(V/a) disjoint intervals on each of which f≥a/2 almost everywhere. One proof is to take the components above an intermediate level t∈(a/2,a) with at most O(1+V/a) intervals, by one-dimensional variation (or group points exceeding a until a drop below a/2; each gap between groups consumes at least a/2 of variation). In such an interval of length l, the two endpoint roles alone give L_f(x)≥(a/2)^(k−1)l/(k−1) almost everywhere in that interval. Its contribution is ≤2al exp(−c_k d a^(k−1)l)≤C_k a/(d a^(k−1)). Summing and using V≥1 gives the bound. The argument works for arbitrary bounded-variation representatives; at an intermediate level the finite-perimeter level set agrees almost everywhere with a finite union of intervals.

For the summation one needs modest uniform growth of R. For some constants c_k>0 and ρ>(k−2)/(k−1),

    R(y)≥c_k (y/x)^ρ R(x)      (integers 1≤x≤y).                            (3)

For k=3 use R(3x)≥2R(x) and ρ=log 2/log 3. Generally choose a fixed large q for which R₃(q)>(2q−1)^((k−2)/(k−1)), possible by Behrend. Use digits from a 3-free subset of [0,q) in base 2q−1 and high positions from a k-free set of length x. Equalities of consecutive second differences force the low digits to form a progression without carry; being 3-free these digits are all equal. Then the high positions form the forbidden k-progression unless constant. Thus R((2q−1)x)≥R₃(q)R(x). Iteration gives (3). [Behrend's lower construction](https://doi.org/10.1073/pnas.32.12.331)

Write a*=(m/d)^(1/(k−1)), T=a*R(m)/m. For a≤a* with d a^(k−1)≥1, apply (3) with x=⌈d a^(k−1)⌉ and y=m. The first layer bound is ≤C_k T(a/a*)^(1−(k−1)(1−ρ)), with strictly positive exponent (ceilings change only a fixed factor). Layers with d a^(k−1)<1 contribute O_k(d^(−1/(k−1))) in total, which is O_k(T) by (3). For a>a*, if m<⌊d⌋ the failure of the defining test at m+1 and R(m+1)≤R(m)+1≤2R(m) imply V≤C_k a*R(m). The second layer bound is then ≤C_k T(a*/a)^(k−1). If m=⌊d⌋, then a*≥(1/2)^(1/(k−1))>1/2 and there is no dyadic layer in this range. The two geometric sums prove the upper side of (1).

## A matching choice of probabilities

Choose a free subset D⊂[0,m) of size R(m). Around each point (j+1/2)/m, j∈D, take an interval of width 1/(4m). On their union set f=a*/2 and set it to zero elsewhere. The total variation is ≤a*R(m)≤V. Any k-progression entirely in the support visits just one interval: rounding its entries to centres changes each second difference by at most 1/(2m), less than the spacing of two distinct mesh values. The corresponding indices must therefore form a progression, which must be constant by freeness. For a root in one interval each role contributes at most (a*/2)^(k−1)/(4m) to L_f. Thus dL_f≤C_k uniformly on the support. Integrating gives S_d(f)≥c_k T.

At saturation, m=⌊d⌋, the construction has variation O(R(⌈d⌉)) and achieves the unrestricted order. Conversely (3) gives T/[R(⌊d⌋)/⌊d⌋]≤C_k (m/d)^(ρ−(k−2)/(k−1)). A constant fraction of the unrestricted optimum forces m≥c'd. Tiling the long interval by shorter ones then gives R(m)≥c''R(⌈d⌉), so V≥a*R(m)≥c'''R(⌈d⌉). Constants here may also depend on the target fraction.

## Reading a logarithmic deficit with variation one

Write D(x)=log(⌈x⌉/R(⌈x⌉)). If 0≤β<1 is fixed and V=d^β, let cβ=(1+(k−1)β)/k. For d sufficiently large the defining scale is not saturated, since R(⌊d⌋)=d^(1−o(1)). The test at m and its failure at m+1 yield

    log m = cβ log d + (k−1)D(m)/k + O_k(1).
    −log S(d,d^β) = (1−β) log d/k + (k−1)D(m)/k + O_k(1).

For y≥x≥1, tiling gives D(y)≥D(x)−O(1), and the ordinary digit product with a Behrend alphabet of length comparable to y/x gives D(y)≤D(x)+O(1+√log(y/x)). For example use q=⌊(y/x+1)/2⌋ at integer lengths, so (2q−1)x≤y; bounded ratios and ceilings are absorbed in the absolute constant. Applying these estimates to m and d^cβ gives D(m)=D(d^cβ)+O_k(1+√D(d^cβ)), solving the elementary quadratic inequality. Therefore

    −log S(d,d^β) = (1−β) log d/k + (k−1)D(d^cβ)/k
                     + O_k(1+√D(d^cβ)).

In particular, for the supremum with variation at most one,

    log(1/[N S(N^k,1)]) ∼ ((k−1)/k) log(N/R(N)).

This follows because the deficit tends to infinity by Szemerédi's theorem. The supremum is defined on one fixed interval by an explicit integral and a fixed variation constraint. Evaluating it to the precision required for a ratio-one equivalent for R(N) remains open.

## Verification

[AffineSampleDeletion.lean](AffineSampleDeletion.lean) proves the exact number of distinct index progressions, the weighted deletion inequality for an arbitrary finite joint law, and the final constant of (2) under its site and edge marginal estimates. Its extremal count is the upstream maxCard for k-term progressions. Compile after [SparseSampling.lean](SparseSampling.lean) and [Doubling.lean](../Doubling.lean). The convolution, variation and asymptotic estimates above are ordinary written proofs.
