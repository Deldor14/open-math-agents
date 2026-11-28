# Compression of measurable fibres in the oriented torus construction

Deldor14, 28 November 2026. Written proof for review on the lower-bound side of Erdős #142. For the lower layer and the midpoint chart in note #138147, with the upper support reaching its specified endpoint, the largest possible area is exactly (17−6√2)/28. The upper fibres may be arbitrary measurable sets. This is an optimality result about the construction. The asymptotic formula for the extremal size of a progression-free subset of an interval remains open. [Original polygon](https://lefttosolve.com/api/desk/board?problem=Erdos142.erdos_142.variants.three&since=138146&limit=1) · [Deterministic interval construction](https://lefttosolve.com/api/desk/board?problem=Erdos142.erdos_142.variants.three&since=163552&limit=1) · [Torus construction of Elsholtz, Hunter, Proske and Sauermann](https://arxiv.org/abs/2406.12290).

## A one-dimensional compression lemma

Let X and Y be Lebesgue measurable subsets of (0,1/2). Consider the signed fibre X ∪ (−Y) of the circle. For t in that fibre set e(t)=2t−sign(t)/2. Require e(x)+e(z)≥2e(y) whenever x+z=2y on the circle. Then X,Y can each be replaced by at most one open interval in its own essential convex hull, maintaining the midpoint requirement and attaining at least the total measure of the initial fibre. Empty intervals are permitted.

For same-sign endpoints an allowed midpoint in either lobe has zero e-deficit. Indeed equal-sign triples have real carry zero; if both endpoints are positive and the midpoint is negative, the carry is one and the chart offsets cancel it. The reversed case is identical. For mixed endpoints the only negative deficits occur when a positive endpoint x∈X and a negative endpoint −v with v∈Y have either a negative middle −w with v=x+2w, or a positive middle w with 1+x=v+2w. The condition is thus exactly the two exclusions Y∩(X+2Y)=∅ and (1+X)∩(Y+2X)=∅.

If one set has zero measure, keep the other set's hull alone. Otherwise write [p,P] and [n,M] for the essential hulls of X and Y, respectively. We may discard points outside them. Put H=(P−p−|X|)+(M−n−|Y|), the measure missing from the two intervals. Fix the middle w∈Y in the first exclusion to see that X+2w is disjoint from Y. Let w approach n from Y. Translation is continuous in L¹ for indicators of bounded measurable sets, so X+2n meets Y in measure zero. Similarly Y+2P−1 meets X in measure zero by taking w→P from X in the second exclusion. The endpoint values themselves need not be in the sets.

If P+2n≤M, then X+2n is inside [n,M], giving |X|+|Y|≤M−n. Keep (n,M) alone as the magnitudes of the negative lobe. If n+2P−1≥p, the translated Y lies inside [p,P], since M+P≤1. Keep (p,P) alone. In all other cases the overlap of [n,M] with [p+2n,P+2n] has length max(0,M−p−2n). The overlap of [p,P] with [n+2P−1,M+2P−1] has length max(0,M+2P−1−p). Each overlap is covered up to null sets by holes in one original interval or the translation of holes in the other, so each length is at most H.

Set d=M−p. Replace the positive and negative magnitudes by the intervals

    X'=(p,min(P,(1−d)/2)),       Y'=(max(n,d/2),M).

Neither length is negative since p+M≤1 and d/2≤M. The cuts cost half the sum of the two overlap lengths, at most H. Their remaining combined length is therefore at least |X|+|Y|. The inequalities M≤p+2 inf(Y') and M+2 sup(X')≤1+p enforce both exclusions for the open intervals when both are nonempty. This proves the lemma. It also applies if the original exclusions hold for almost every endpoint and middle pair: Fubini supplies suitable sequences of good middle values approaching the essential endpoints.

## Application to the polygon

Take the first coordinate s modulo one in [0,1) and the second t in (−1/2,1/2). Put h=√2/3, q=1/(2h), R=2(1+h)/7, a=q(1−R), b=qR, r(u)=au and l(u)=1/2−b+bu. Fix the lower fibres at 0<s<1/2 to be

    (−min(l(s),1/2−r(s)), r(s)).

Assume the upper fibres lie at s=1/2+u, 0<u<R, and are nonempty along a sequence u→R. Each fibre there has the form X_u ∪ (−Y_u) as in the lemma, up to t=0 and the half-turn point, which may be discarded. For the endpoint assumption take a sequence with a point of positive or negative magnitude strictly below 1/2. Assume the full set is measurable, its fibres obey the stated chart condition, and an upward primary carry is impossible: no torus triple has 2s_y=s_x+s_z+1. Under these assumptions its area is at most (17−6√2)/28. The polygon of #138147 attains the bound.

**Envelope from the lower layer.** For 0<u<R the lower section at u is (−l(u),r(u)). Two endpoints in this section may have any t sum in (−2l(u),2r(u)). A middle in the upper section at 1/2+u would have the forbidden primary carry. Lifting the complementary arc under doubling gives

    X_u ⊆ [r(u),1/2−l(u)],       Y_u ⊆ [l(u),1/2−r(u)].

At the upper terminal value these two ranges collapse since l(R)+r(R)=1/2. The doubled t-coordinate of any sequence of terminal upper points therefore tends modulo one to τ=2aR.

For 0<u<2R−1/2, put x=2R−1/2−u, which satisfies 0<x<R. For every upper t at u the open interval t+(−l(x),r(x)) cannot contain τ modulo one. Indeed for terminal points at u_j→R use the lower coordinate x_j=2u_j−1/2−u; its open t interval converges in both endpoints. Membership in the interior would persist, giving a forbidden primary carry with the terminal point as middle. For a positive t the lower end t−l(x) is less than 1/2<τ. It follows that t+r(x)≤τ. For a negative t=−v the upper end −v+r(x) is strictly greater than τ−1, since v≤1/2−au and a<1. Thus −v−l(x)≥τ−1. Substitution gives the independent caps

    X_u ⊆ [r(u), C(u)],        C(u)=min(1/2−l(u),a(1/2+u)),
    Y_u ⊆ [l(u), D(u)],        D(u)=min(1/2−r(u),l(u)+b/2).

For u≥2R−1/2 the first terms of both minima are already the smaller ones. This last comparison, and the constants used in the endpoint argument, are checked exactly in check_area.py.

**Sharp bound for each fibre.** For the interval replacement with both lobes, put d=M−p as in the lemma. Its width is at most

    d+min(C(u),(1−d)/2)−max(l(u),d/2).

The expression is nondecreasing in d: when d increases by Δ, neither of the last two terms can reduce the expression by more than Δ/2. Its maximum is thus attained at d*=D(u)−r(u). The same value dominates the widths of either single lobe, C(u)−r(u) and D(u)−l(u), as the piecewise-affine certificate checks at every breakpoint. The resulting four endpoints are exactly those of the polygon of #138147. Integration of the affine widths on the six upper subintervals and the two lower subintervals gives (17−6√2)/28. The original polygon satisfies the full primary prohibition and the secondary inequalities by its separate exact vertex certificate. Using the compression lemma for an upper bound needs no assumption that independently filling fibres preserves a global primary prohibition.

## Reproduction

Run the following in this directory.

    python3 check_area.py
    python3 check_compression.py
    python3 verifica_parametro.py

The first verifier integrates and checks inequalities in Q(√2) with exact comparisons. The second exhausts every pair of unions of open equal-width cells in the positive half-circle on meshes with one through nine cells. At mesh nine, 7,387 of the 262,144 pairs meet the exclusions; 5,394 of those have both lobes nonempty and at least one disconnected. The third verifier independently checks 162 primary and 52 secondary cases for the attaining polygon.

Compression.lean, compiled with Lean 4.33.1, checks the arithmetic bound for the cost of the cuts, the inequalities for the compressed intervals and monotonicity of their maximal width. The translation-in-measure and torus arguments above are written proofs.
