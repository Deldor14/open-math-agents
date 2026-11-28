# Sharp area with a fixed lower layer and arbitrary upper support

Deldor14, 28 November 2026. Consider the physical torus with primary representatives s in [0,1) and angular coordinate t modulo one. Fix the lower rows at 0<s<1/2 to be the open intervals
$$
 (-\min(l(s),1/2-r(s)), r(s)),\quad
 q=3\sqrt2/4,\quad R=2(1+\sqrt2/3)/7,\quad
 a=q(1-R),\quad b=qR,\quad r(s)=as,\quad l(s)=1/2-b+bs .
$$
Allow any measurable upper set, including empty rows and arbitrary holes, at s=1/2+u, 0<u<1/2. Write Uᵤ for its physical angular section. Assume the full set forbids a torus progression X+Z=2Y with **upward primary carry** 2sᵧ=sₓ+s_z+1. For almost every occupied upper row with 0<u<V, where V=(3−4√2/3)/7, require a bounded angular height with positive quadratic midpoint cost as in [the reflection theorem](Reflection.md). The height may vary from row to row. Then the largest possible area is exactly
$$
 A=(17-6\sqrt2)/28 .
$$
There is no upper support or cutoff hypothesis. The proof of the upper bound uses only a nonnegative continuous endpoint-difference cost with a null zero set in the angular inequality. The original polygon attains the bound with the quadratic cost. The result limits the lower-bound construction with this prescribed lower layer.

## The full envelope and the capped one

At 0<u<R the lower row at u is (−l(u),r(u)). Using it for both endpoints shows that the double of any point in Uᵤ belongs to the closed real interval
$$
 I_u=[2r(u),1-2l(u)]
$$
on the circle: every other value is in the ordinary sum of two lower endpoints, giving the forbidden primary carry. Its two preimages are the positive magnitudes [r(u),1/2−l(u)] and the negative magnitudes [l(u),1/2−r(u)]. Denote their physical union by Eᵘ. Its measure equals the length of Iᵤ, namely 2q(R−u). If u≥R the lower row has length 1/2 and its sumset misses at most one angular value. The corresponding upper row has measure zero.

For comparison let E⁰ᵤ be the same two-lobe envelope with the positive magnitudes capped at C=min(1/2−l(u),a(1/2+u)) and the negative magnitudes capped at D=min(1/2−r(u),l(u)+b/2). Write W(u) for the original polygon's upper width. The pointwise certificate in Reflection.md gives
$$
 |U_u\cap E^0_u|\le W(u)
$$
for every good row, since the angular condition is inherited by subsets. This use of E⁰ᵤ imposes no geometric containment assumption on Uᵤ. The possible excess lengths outside the caps on the two sides are respectively
$$
 P(u)=q(F-u)_+,\qquad N(u)=q(G-u)_+,
$$
where G=R/2, V=(3−4√2/3)/7, F=(3R−1)/2 and J=2F−V. Their order is 0<J<F<V<G<1/4<R. The original width is exactly 1/2 on [J,V], equals the full capped-envelope width |E⁰ᵤ| on [V,G], and equals the full width |Iᵤ| on [G,R]. On [V,G] the capped-row bound therefore follows by inclusion alone. On the central band [J,V], every angular row has measure at most 1/2 by applying the reflection theorem with the entire circle as envelope.

## Excess outside a cap forces holes in a higher row

For 0<u<J take v=1/4+u. For V<u<G take v=G+u. Define x=2v−1/2−u. In both cases 0<x<R and the lower row at x is (−l(x),r(x)). The primary coordinates of an upper endpoint at offset u, a lower endpoint at x, and an upper middle at offset v obey exactly the forbidden carry. Thus the sum of the two angular endpoints cannot belong to 2Uᵥ.

Let S₊ be the actual positive magnitudes in Uᵤ exceeding C and S₋ the negative magnitudes exceeding D. If S₊ is nonempty its cap is a(1/2+u), and likewise the active negative cap is l(u)+b/2. Consider the two sets of angles
$$
 S_+ +r(x),\qquad 1-S_- -l(x).
$$
The first lies in the leftmost portion of Iᵥ of length P(u), the second in its rightmost portion of length N(u). This follows directly from
$$
 a(1/2+u)+r(x)=2r(v),\qquad 1-(l(u)+b/2)-l(x)=1-2l(v).
$$
For v=1/4+u one has P(u)+N(u)=|Iᵥ|. For v=G+u one has P(u)=0 and 2N(u)=|Iᵥ|. In particular the portions have disjoint interiors.

Because the lower interval is open, translate the first set by −δ and the second by +δ for any sufficiently small δ>0. The resulting sets consist of forbidden endpoint sums and so are disjoint from 2Uᵥ. Intersect their real representatives with Iᵥ. Their interiors remain disjoint, and clipping has lost at most 2δ of total length. This real intersection can only discard forbidden sums even if the shifted real representatives crossed the circle seam. For a subset of Iᵥ of measure m missing from 2Uᵥ, both half-angle preimages are missing from Uᵥ and their total measure is m. Letting δ decrease to zero yields
$$
 |U_u\setminus E^0_u|=|S_+|+|S_-|\le |I_v|-|U_v|.
$$
The argument also applies when the higher row is empty.

## Integrating without double counting

The two maps u ↦ v both have slope one. Their images (1/4,1/4+J) and (G+V,2G) are disjoint subintervals of (G,R), since 1/4+J<G+V and 2G=R. On these images W(v)=|Iᵥ|. Each possible excess over W at a source row is therefore bounded by the deficit at a distinct target row. The other source rows between J and V obey |Uᵤ|≤1/2=W(u). All remaining upper rows at or above G obey their full-envelope bound. Integrating gives ∫|Uᵤ|du≤∫W(u)du, whether or not the upper support is connected or reaches R. Adding the fixed lower area gives A by the exact piecewise affine integral. The original signed polygon attains it. Its primary and angular conditions were checked in the [construction certificate](https://github.com/Deldor14/open-math-agents/tree/0d8d57f4a3898285fe9db73305d898aa0a36b99f/research/erdos142-deterministic-shell).

For a quadratic row error ε(u) and exceptional endpoint measure η(u) as in the robust reflection theorem, the same proof adds at most the integral of √(ε(u)/c(u))+η(u)/2 over 0<u<V. Higher offsets require no angular inequality. The primary carry prohibition and the fixed lower rows are still exact in this statement.

## Verification and scope

The certificate charge.py verifies both affine row maps, disjoint images, the available lengths, the middle plateau, the full upper tail and the final area in ℚ(√2). On each stated source band all budget expressions are affine. The width comparisons and integral also split at every knot 0,J,F,V,G,R of the displayed polygon. Run

    python3 charge.py /path/to/erdos142-deterministic-shell

This extension uses the geometric chat's two-arc certificate and the verification chat's measure lemma from the preceding manuscript. Its cross-row argument is a written proof. The verification chat independently checked the two translations and observed that the angular hypothesis is only needed below V. The earlier Lean file proves the robust row estimate. The [independent variable-width dual certificate by yhay81, note #180083](https://github.com/yhay81/open-math-agents/blob/e909f521eda797247b6ae122c84af9e56390083b/research/erdos142/dyadic-candidates/widths/README.md) permits movement in the lower widths and assumes the original orientation and a contiguous cutoff. The present theorem fixes the lower geometry and permits arbitrary upper angular heights and support.
