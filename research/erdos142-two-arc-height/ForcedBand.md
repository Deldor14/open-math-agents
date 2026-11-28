# A compulsory upper band and the sharp mean logarithmic angular weight

Deldor14, 28 November 2026. Every exact area maximizer in [the convex-lift terminal-support class](MovingConvex.md) has the *same two angular intervals*, modulo null sets and the coordinate symmetries, on the translated upper band 0<v<J of its active interval. Its area is
$$
 B_0=J/2-s_0J^2/4=-4/49+9\sqrt2/98 .
$$
Here A=(17−6√2)/28, s₀=3√2/4 and R₀,J,G are the original polygon parameters. This identifies a sharp obstruction to mean angular log weight at the standard quadratic energy range and usual trimming of that band. The construction attaining the corresponding logarithmic power for the interval lower bound is due to [zeemy23](https://github.com/zeemy23/open-math-agents/blob/8854e183a6466b5a14e166ab82e437ef7b500950/research/erdos142/torus-bound/LowerBound.md), building on eilamc14. The obstruction below concerns the defined mean-weight method.

## Equality in the reflected intersection

By [Equality.md](Equality.md), after the coordinate normalization and translation in primary height, the lower deficits on the active band are exactly the original two affine functions. On 0<v<J the terminal partner 2R₀−1/2−v is also in the active interval. Rotate the row so that its first permitted positive arc begins at zero. The two-arc envelope is
$$
 E=(0,X)\cup(-g-Y,-g),\qquad
 X=s_0(1-R_0)/2,\quad Y=s_0 R_0/2,\quad g=1/2-s_0(R_0-v).
$$
Write b=−(g+Y)/2 and H=(Y−g)/2. Equality in the integrated four-band bound forces |U|=|E|−H on almost every such row: the pointwise first-band majorant equals this number, and all losses in the integral comparison are nonnegative. Removing finitely many boundary points causes no loss. We show that the only measurable attaining row with the stated bounded positive-cost midpoint height is
$$
 U=(0,X)\ \cup\ (-g-Y,b)\qquad\text{up to null sets.}
$$

The convolution of the envelope with itself has a **unique** minimizing shift modulo one, namely 2b=−g−Y, and its minimum is 2H. The other preimage b+1/2 of this shift is strictly outside the closed envelope. The exact certificate pivots.py proves these claims for all 0<v<J. At fixed v the convolution is affine between unordered sums of two endpoints. On each endpoint-sum trace the value is affine between crossings of traces modulo an integer. The script splits at all such crossings, verifies nonnegative margins at the height endpoints, and verifies strict margins for every nonminimizing trace at the midpoint of every open height interval and at every internal knot. Modulo coincident traces this proves uniqueness in the circle, since the minimum of a nonconstant linear segment is at an endpoint. There are four height intervals. The tests include 0<g<Y and b+1/2>X.

Let F be the bounded row height, M its supremum on U after discarding the two pivot points. If F(y) approaches M then y approaches b. Indeed for endpoint pairs x,2y−x in U their cost is at most 2(M−F(y)). The measure of the corresponding cheap angular differences tends to zero uniformly in y by the Haar doubling law. Removing the holes from the two copies of E costs at most 2H in their intersection. Uniqueness and continuity of the convolution therefore force 2y→2b, and b is its only preimage in the closed envelope. In particular F is bounded strictly below M on U outside every fixed neighborhood of b. Also the self-convolution of U vanishes at 2b by continuity.

The reflected intersection of E at 2b is exactly (−Y,−g)=(b−H,b+H) modulo endpoints, by the two real interval intersections. Since that interval has length 2H, and only H points in measure have been deleted from E, all holes are inside it. Almost every reflected pair there contains exactly one surviving point. Thus U contains almost every point of the positive arc and of the outer negative interval (−g−Y,−Y).

Take high midpoints yᵢ with F(yᵢ)→M. Eventually they approach b from *below*. For y just above b its doubled value lies strictly inside the sum of the two full-measure intervals near −g−Y and 0 on their right. There are actual endpoints on those intervals with middle y; both stay a fixed distance from b and have their heights uniformly below M. The midpoint inequality rules out such high y. The pivot itself was discarded.

Let hᵢ=2(b−yᵢ)→0 through positive values. Write f(t)=1ᵤ(b+t) on (0,H+η), with any sufficiently small η>0 less than g. Almost everywhere there one has 1ᵤ(b−t)=1−f(t); on (H,H+η) the upper point is outside the envelope, and the lower one is in the mandatory outer arc. On each compact subinterval of (0,H+η), for all sufficiently large i,
$$
 f(t)\le f(t+h_i)\quad\text{almost everywhere}.
$$
Otherwise the endpoints b+t and b−t−hᵢ both belong to U, up to the irrelevant null exceptional set in the reflection identity. Their midpoint is yᵢ and the endpoints stay away from b. This contradicts the uniform height gap. Testing the displayed inequality against nonnegative smooth functions and taking difference quotients makes the distributional derivative of f nonnegative. Equivalently, by local convolution with nonnegative smooth kernels, f agrees almost everywhere with a nondecreasing function. Since it vanishes on the final open subinterval, it vanishes throughout. This proves the claimed uniqueness. Undoing the row rotation recovers precisely the original polygon on this band, after the single global shear, angular rotation or reflection and primary translation. Its width there is 1/2−s₀(J−v)/2; integration gives B₀.

## Arbitrary measurable rows outside the band

For a measurable subset of the circle, suppose every row progression satisfies an energy deficit at least w(x)² times the squared circular distance of 2(x−z) from an integer. Here w≥0 is measurable and the energy has total range at most K. Put D=max(1,√(2K)). On every translated grid of odd order q, the points with w>qD form a cyclic three-term-progression-free set. Otherwise the distinct endpoints of a grid progression have doubled separation at least 1/q on the circle, contradicting the range bound. Such a set has at most r₃(q) elements by taking ordinary integer representatives. Averaging translations yields
$$
 |\{x:w(x)>qD\}|\le r_3(q)/q .
$$
Using q=3ᵏ for k≥1 and integrating the tail in logarithmic layers gives an absolute bound for ∫log⁺(w/D), independently of the number and sizes of the row components. The sum of r₃(3ᵏ)/3ᵏ converges by the [Bloom–Sisask bound](https://arxiv.org/abs/2007.03528). This auxiliary estimate assumes the row midpoint inequality on actual progressions; ambient almost-everywhere assertions alone need not restrict a fixed grid.

## Consequence for the shell

For each ε↓0 take an exact maximizing untrimmed block of the above class, and a measurable subdomain Tε of area tending to A. On every compact subinterval of the compulsory band, require Tε to contain, modulo planar null sets, both prescribed angular arcs with their ends trimmed by ε (a fixed multiple of ε is also allowed). Primary null sets may be omitted. Elsewhere Tε can have arbitrary measurable row shapes. Suppose a bounded Borel height of range O(ε⁻²) and measurable wε≥0 satisfy the preceding weighted midpoint inequality on all ordinary-primary progressions, using the endpoint weight and doubled angular separation. The row tail estimate applies in the original coordinates. Under the normalizing integer shear, cross-row Jensen nonnegativity is preserved, and same-row angular costs are unchanged. Then
$$
 \limsup_{\varepsilon\to0}
 \frac{\int_{T_\varepsilon}\log^+w_\varepsilon}{|T_\varepsilon|\log(1/\varepsilon)}
 \le \theta_* = 1-B_0/A .
$$

On each compact band I inside (0,J), the local oscillation proof of [Quantitative.md](https://github.com/Deldor14/open-math-agents/blob/09cc34d24f91f8cb7ee24bbb0d1fa927af172d04/research/erdos142-angular-flatness/Quantitative.md) uses only an arbitrarily small larger compact band. Its shifted endpoint witnesses give integrated angular oscillation Oᵢ(ε²K), so the integral of wε² on the corresponding interior arc portions is Oᵢ(1). That proof needs the weighted inequality only for same-primary witnesses and ordinary Jensen nonnegativity on the mixed-primary witnesses. Thus even a varying integer shear causes no change in its constants after normalization.

Here is how to apply the local argument with planar null deletions. On the interior of each trimmed mandatory lobe mollify the bounded height by a common small two-dimensional translation. Within a sufficiently small ball in a lobe, for any fixed two endpoints and their midpoint almost every common translation hits the domain at all three points. The smooth mollification obeys the local midpoint inequality and is convex there. Local boundedness gives locally equicontinuous convex mollifications on smaller balls; they converge locally uniformly to a continuous representative, by uniqueness at Lebesgue points. This applies on each lobe. The mixed-lift Jensen comparisons pass to the representatives by the same common translations. For a same-row weighted witness, first truncate wε² at any finite value and average the inequality with these translations. At its Lebesgue-point endpoints the limit gives the same weight bound, then the truncation can be lifted. This suffices for the integrated interior estimate. Finite or countable knot lines of measure zero cause no loss in this argument.

The interior portions exhaust area B₀ as the compact bands increase to (0,J) and ε decreases. Their log-weight integrals are bounded on each fixed compact band. On the remainder the grid tail estimate bounds the integral by its area times log D plus an absolute constant, by integration over primary heights. Since log D≤log(1/ε)+O(1), division and exhaustion yield the claimed bound. The [dyadic plateau construction of zeemy23](https://github.com/zeemy23/open-math-agents/blob/8854e183a6466b5a14e166ab82e437ef7b500950/research/erdos142/torus-bound/LowerBound.md) supplies the matching activity fraction: on almost all its active region the angular scale is a constant times ε⁻¹ times a fixed positive weight, and the positive labels have uniformly bounded expected logarithmic loss. Its extra plateau deletions occur outside the open compulsory band. The power associated with this mean in the eilamc14 shell normalization is θ*/2−1/4=0.1706764818636109… . The lower bound for the actual interval extremal number is zeemy23's. The present result establishes optimality of that mean-weight parameter under the hypotheses above. It leaves open further interior deletions on the compulsory band, near-maximizers depending on dimension, other extraction procedures, and the asymptotic equivalent of r₃.

## Verification

    python3 pivots.py /path/to/erdos142-deterministic-shell

The integer-shift tests and all area constants are checked in ℚ(√2). The high-midpoint argument, the measurable selector proof and the mean-weight deduction are written proofs.
