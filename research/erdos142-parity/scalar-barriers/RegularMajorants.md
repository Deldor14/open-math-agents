# How closely a regularly varying majorant can follow the Roth numbers

Write R(n) for the maximum size of a three-term-progression-free subset of [0,n). For j≥0 let D(j)=log₂(2ʲ/R(2ʲ)). Define the extended real number

    C = 2 ^ { sup over integers l≥1 of limsup as j→∞ [D(j+l)−D(j)] }.

The order of the limits matters. For each fixed window length l, only the far tail of the dyadic density is measured.

**Theorem.** For every prescribed function g on the positive integers tending to infinity there exists a nonnegative concave function V on [0,∞), regularly varying of index one, with V(0)=0 and V(n)≥R(n), such that

    V(n) ≤ g(n)R(n) eventually,     liminf V(n)/R(n) = 1,     limsup V(n)/R(n) = C.

Every regularly varying majorant of index one has limsup at least C. The optimizing V can simultaneously be chosen to satisfy, for all real x,y≥1,

    V(x)V(y) ≤ V((2x−1)y),
    V(x)+V(y) ≤ V(x+2y−1)  if x≤y.

It satisfies rV(x)≤V(Lx−b) for all integers L≥1 and 0≤b≤L−1 and real r≥0 for which rR(n)≤R(Ln−b) holds at every integer n≥1. V is subadditive, nondecreasing, 1-Lipschitz and V(x)/x tends to zero. In particular C=1 precisely if R itself varies regularly with index one. The value of C for the true R is unknown here. The majorant uses R as input. An explicit asymptotic equivalent for Erdős #142 remains open.

The comparison also applies to the scalar example with recurrent Fibonacci plateaus. For that example a choice of increasingly separated transitions gives **C=987/128 exactly**. Thus an irregular integer model and a regularly varying concave majorant can stay within a bounded factor while both preserve the nonlinear digit inequality and the common affine digit rules. The stated constant is optimal for that model.

## Two finite comparisons

Tiling gives R(k)≤⌈k/n⌉R(n) for positive integers k,n. No-carry digits give R(q)R(k)≤R((2q−1)k). For integers n≥k, take q=⌊(n/k+1)/2⌋, so n/(3k)≤q≤n/k. The classical Behrend lower bound R(q)≥c q exp(−A√log q), with fixed c,A>0, now gives

    R(k)/R(n) ≤ B (k/n) exp(A√log(n/k))                                      (1)

for an absolute B≥1. These inputs also hold with the integer model H of [the nonlinear digit theorem](SelfConsistentDigits.md) throughout, since H≥R and H has its own digit product. Other qualitative inputs used below are R(0)=0, R(1)=1, 1≤R(n)≤n, monotonicity, R(n)=o(n) and the affine join 2R(n)≤R(3n−1). They hold for H as well. [Mathlib Behrend estimate](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Additive/AP/Three/Behrend.html) · [Dyadic deficit and digit input](MatchedDeficit.md)

Write dₙ=R(n)/n. For each fixed Q≥1 one has

    limsup as n→∞ of max {dₖ/dₙ : n/Q≤k≤Qn} ≤ C.                               (2)

Indeed choose 2ʲ≤n<2ʲ⁺¹, a=2^(j−h), b=2^(j+h) with fixed h large, and j≥h. Tiling gives dₖ≤(1+a/k)dₐ and d_b≤(1+n/b)dₙ. The ratio dₐ/d_b equals 2^[D(j+h)−D(j−h)], and the two error factors are at most 1+Q2^(−h) and 1+2^(1−h). First pass to the limsup, then send h to infinity. Conversely k=2ʲ and n=2^(j+l) recover each fixed-window term in C. Tiling at k>Qn also gives dₖ/dₙ≤1+1/Q. Consequently when C is finite, for every fixed Q the limsup of the largest density ratio over **all** integers k≥n/Q is ≤C, by enlarging the upper cutoff and using C≥1.

If W≥R is regularly varying of index one, W(2^(j+l))/W(2ʲ)→2ˡ for each fixed l. Therefore limsup W(n)/R(n) is at least limsup d_(2ʲ)/d_(2^(j+l)) for each l. This proves the lower bound C without any other hypotheses on W. Regular variation here means W(λx)/W(x)→λ for every fixed real λ>0.

## A multiplier adjusted to the permitted error

Choose positive step sizes δᵢ=1/(i+2), i≥1, and increasing thresholds tᵢ→∞. Let δ(t) decrease to zero, taking the value δᵢ on [tᵢ,tᵢ₊₁) before the following lower adjustment. Take δ=δ₁ on the initial interval. Replace δ(t) by the maximum of itself and min(δ₁,(A+2)/√(1+t)). This is still nonincreasing, bounded above by 1/3, and tends to zero. Put

    w(t)=∫₀ᵗ δ(s) ds,      F(x)=x exp(−w(log x))       (x≥1).

Here and below the unmarked logarithm is natural. F is increasing, F(x)/x decreases to zero, and F is regularly varying of index one. The lower adjustment and Behrend ensure R(n)/F(n)→∞. The integral cost has decreasing increments. For y≤n and tᵢ≤log n<tᵢ₊₁ we have F(n)/F(y)≤(n/y)^(1−δᵢ). Set

    J(x)=max_{integer 1≤k≤x} R(k) F(x)/F(k)         (x≥1).

This is nondecreasing and ≤x. It majorizes R at integers and J(y)/F(y) is nondecreasing. By (1), J(n)/R(n)≤B exp(A²/(4δᵢ)). Define tᵢ large enough that 3B exp(A²/(4δᵢ))≤g(n) whenever log n≥tᵢ. This is possible even for nonmonotone g.

When C is finite we impose an additional choice. For each i choose Qᵢ large enough that B exp(A√s−δᵢs)≤1 for s≥log Qᵢ. By (2) and the following unbounded-tail comparison, choose the same tᵢ large enough that dₖ/dₙ≤C+1/i for all k≥n/Qᵢ and log n≥tᵢ. For k≤n/Qᵢ, (1) times the multiplier then bounds its contribution to J(n) by R(n). For n/Qᵢ<k≤n, use F(n)/F(k)≤n/k. Thus J(n)≤(C+1/i)R(n) throughout this stage. All threshold choices are lower bounds, so they can be satisfied together.

## Exact operations before and after taking the concave majorant

For real x,y≥1 take maximizing integer witnesses u≤x and v≤y. Write z=(2x−1)y, h=(2u−1)v, h'=uv(2−1/x). Then h≤h'≤z, h'≥u,v and z/h'=(x/u)(y/v). By decreasing increments of w, splitting the interval from log h' to log z at distance log(x/u) gives

    w(log z)−w(log h') ≤ [w(log x)−w(log u)] + [w(log y)−w(log v)].

Consequently F(z)/F(h)≥F(z)/F(h')≥[F(x)/F(u)][F(y)/F(v)]. Use the integer witness h and the true digit inequality there to get J(z)≥J(x)J(y). Likewise if rR(m)≤R(Lm−b), put z=Lx−b, h=Lu−b, h'=u z/x. Now h≤h', h'≥u and z/h'=x/u. The same cost inequality gives J(z)≥rJ(x).

For x≥1 let V(x) be the supremum of E J(X) over finitely supported real random variables X≥1 of mean x. This is finite since J(X)≤X, and concatenating mixtures proves concavity. We have V(1)=1; extending by V(x)=x on [0,1] is concave because V(x)≤x on the positive ray. V is unbounded and nonnegative on the ray, hence nondecreasing. Its initial line and concavity give subadditivity and the Lipschitz bound. Moreover J(x)/x→0: old witnesses k≤K have F(x)/x→0, and the others contribute at most sup_{k>K} R(k)/k. Any bound J(x)≤εx+constant transfers to V, proving V(x)/x→0 as well.

Independent witnesses X,Y for two means x,y give E[(2X−1)Y]=(2x−1)y and E[J(X)J(Y)]=E[J(X)]E[J(Y)]. Taking suprema preserves the nonlinear digit inequality. An affine rule transfers directly by taking the random variable LX−b. In particular 2V(y)≤V(3y−1). The increments of a concave function over intervals of the same length decrease with the starting point. Taking this length to be 2y−1 yields the claimed two-input join at every 1≤x≤y. The [Lean certificate](RegularHull.lean) proves the two finite mixture transfers, the product identity for h', and the split of a decreasing-increments cost.

For fixed λ≥1 and any ε>0, regular variation of F gives J(λy)≥λ(1−ε)J(y) for all y≥T with T large, by retaining the maximizing witness. For an arbitrary finite mixture of mean x, the total weighted contribution of y<T is at most J(T). Scaling the mixture therefore gives V(λx)≥λ(1−ε)(V(x)−J(T)). Concavity through zero gives the reverse bound V(λx)≤λV(x); V(x)→∞. This proves regular variation, also for λ<1 by inversion.

## The sharp upper bound and the points of contact

For y≥n the witnesses k≤n contribute at most (y/n)J(n). For the witnesses k>n the contribution is at most y sup_{k≥n} dₖ. In particular J(y)≤2(y/n)J(n), by tiling. For y≤n we have J(y)≤J(n), so the affine bound J(y)≤(1+2y/n)J(n) proves V(n)≤3J(n) and hence the prescribed eventual bound with g.

We use ηₙ=sup_{1≤y≤n}(F(y)/F(n)−y/n), which tends to zero. To see this, use monotonicity and regular variation at each point of a fixed finite uniform grid in [0,1]. Below its first positive point use monotonicity alone, then let the mesh tend to zero. For y≤n we consequently have J(y)≤(y/n+ηₙ)J(n). In the finite-C construction, for y≥n the preceding witness bound and the choice of tᵢ give J(y)≤(C+1/i)(y/n)R(n). The affine majorant valid for all y≥1 now gives V(n)≤(C+1/i)(1+ηₙ)R(n). This proves that the sharp limsup is attained. If C=∞ the necessary lower bound already gives the limsup.

There are unbounded record integers n for R(n)/F(n), because this ratio tends to infinity. At each such n, J(n)=R(n) and every 1≤r≤n has R(r)≤(r/n+ηₙ)R(n). Division of any integer k≥n into copies of n and a remainder gives dₖ≤(1+ηₙ)dₙ, using R(0)=0 for zero remainder. For y≥n it follows that J(y)≤(1+ηₙ)(y/n)R(n). For y≤n use the preceding bound on J(y). One affine majorant of these two expressions gives V(n)≤(1+2ηₙ)R(n). This proves the liminf. If C=1 the two-sided squeeze transfers regular variation to R (with integer parts for its arguments). Conversely a regularly varying R has D(j+l)−D(j)→0 for each fixed l.

## An irregular model with an exactly computed constant

For the model H of [SelfConsistentDigits.md](SelfConsistentDigits.md) replace its dyadic clock S(i) by S(i)+i⌊log₂(i+1)⌋. The added integer term is superadditive and its successive increments tend to infinity. All lower spacing requirements are preserved. Its contribution to the upper estimate on e(S(i)) is O(√(i log(i+1))) by the Behrend upper envelope for e and subadditivity. Hence the unconditional pointwise estimate in [MatchedDeficit.md](MatchedDeficit.md) persists, as do the optional finite prefix and the affine rules there.

The ratio between successive starting positions now tends to infinity. Any fixed multiplicative window meets at most one transition eventually. Across that window the modeled density is between the two consecutive slopes, up to a vanishing relative rounding error. The outgoing slope divided by the incoming slope is κᵢ=128/987+(1−128/987)2⁻ⁱ, tending to 128/987. Let W be the fixed endpoint multiplier of a transition and l=⌈log₂W⌉. The dyadic window [Nᵢ,2ˡNᵢ] starts at the incoming slope and finishes on the outgoing line before the next transition, for every sufficiently large i. Its limiting density ratio is 987/128, proving equality directly in the definition of C. Applying the theorem to H gives the asserted sharp companion. The actual Roth number has not been shown to exhibit this drop.

Bounds such as (1) belong to the theory of O-regular variation and global growth indices. The formula above uses the full density loss on fixed dyadic windows and preserves the arithmetic rules of the particular input. The global optimization and asymptotic passages are written proofs. [Bingham, Goldie and Omey on growth indices](https://www.ma.imperial.ac.uk/~bin06/Papers/bgo.pdf)
