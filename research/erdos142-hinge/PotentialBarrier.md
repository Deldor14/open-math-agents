# Sharp oscillation and standard-deviation costs for the eroded signed torus block

Let Bη be the signed six-width block at the optimal parameters of CubeJerry's note 136918, with both angular ends of every interval shaved by η and the interface |s−1/2|≤η removed as in SignedEndpoint.md. Write d for distance modulo one on the angular circle. Suppose a bounded real function F on Bη satisfies, for every modular three-term progression x+z=2y in the block,

    F(x)+F(z)−2F(y) ≥ κ d(a_x,a_z)²,    κ>0.                       (1)

There are constants c>0 and η₀>0 depending only on the fixed profile such that

    sup F − inf F ≥ c κ / η²    whenever 0<η<η₀.                    (2)

For bounded measurable F there are profile-dependent constants c′,p₀>0 such that for every real c₀ the Haar area of {x∈Bη : |F(x)−c₀|>c′κ/η²} is at least p₀. This gives the same order lower bound for the mean absolute deviation from any level and for the standard deviation under uniform probability on Bη.

The order is attained: the potential in SignedEndpoint.md with A=12/η² has (1) with κ=1 and oscillation at most A+1. In particular the full unshaved signed block cannot support a bounded potential with (1) and κ>0. Neither measurability nor continuity in height is assumed. The assertion concerns this particular block and this pointwise curvature requirement.

## An affine part of the signed profile

Work with upper heights s=1/2+t on a compact interval around t₀ lying strictly inside the first open switching regime 0<t<m₀. Put r=p+q. In the folded coordinate u=a−1/2 on the positive sheet and u=a on the negative sheet, write the intervals as

    (l(t),a(t)) on the positive sheet,   (b(t),z(t)) on the negative sheet,

where l=(−1−V)/4, a=(−1+P)/4, b=(−1−M)/4 and z=(−1+U)/4. All four are affine here, and l<b<a<z. Indeed V>M, P<U and P+M>0 in this open regime. Further,

    b(t) < z(t)−1/4 < a(t).

The first inequality is U+M>1, since U+M=p>1, and the second is U−P<1. These inequalities are strict on a compact neighborhood of t₀ and therefore survive sufficiently small shavings. Their hypotheses follow directly from U=1−2pt, M=p−1+2pt, P=2w+q−1+2qt and V=(2−U−P)/2. This applies also to the rational benchmark (p,q,w)=(69/56,25/28,3/28).

At a fixed height, F takes the same value at both representatives of any overlap point: each is a modular midpoint of the other taken twice, and (1) holds in both directions. Denote the common folded function by f_t on the union of the shaved intervals. On each individual interval it is midpoint-convex, by ordinary angular progressions on one sheet. A bounded midpoint-convex function on an open interval is convex (dyadic Jensen inequality and continuity on the interior). Two convex functions agreeing on an open overlap give a locally convex function there and hence a convex function on the entire interval union. Only this one-dimensional consequence of boundedness is needed.

## Two linked families of actual progressions

Choose e=2η and τ=8e/r. Fix σ>0 so that [t₀−σ,t₀+σ] lies inside the neighborhood above. Let m=⌊σ/τ⌋ and t_i=t₀+iτ for −m≤i≤m. For small enough η we have m≥2. At each height define

    L_i=f_{t_i}(l(t_i)+e),   A_i=f_{t_i}(a(t_i)−e),   R_i=f_{t_i}(z(t_i)−e).

All three points are strictly inside the eroded block on the indicated sheets. Let v=z(t_i)−e−1/4. Both sheet representatives of v exist. The two antipodal points with angles v+1/2 and v have an ordinary midpoint of angle v+1/4=z(t_i)−e on the negative sheet. Equation (1) gives

    f_{t_i}(v) ≥ R_i + κ/8.

At this height, both v and a(t_i)−e are between l(t_i)+e and z(t_i)−e. By convexity their values are at most max(L_i,R_i). It follows that H_i=L_i−R_i≥κ/8 and D_i=A_i−R_i≤H_i. In particular

    2L_i−A_i−R_i = 2H_i−D_i ≥ κ/16 + |D_i|/2.                     (3)

The second progression runs between heights. Use the positive right point a(t_{i+1})−e at height t_{i+1}, the negative right point z(t_{i−1})−e at t_{i−1}, and the positive left point l(t_i)+e as midpoint at t_i. The folded discrepancy is exactly +1/2, because

    P(t+τ)+U(t−τ)+2V(t) = 2+2rτ,    e=rτ/8.

Restoring the sheet labels gives an exact ordinary angular midpoint. Hence (1) implies 2L_i≤A_{i+1}+R_{i−1} for |i|<m. Combining with (3),

    κ/16 + |D_i|/2
      ≤ D_{i+1}−D_i + R_{i+1}−2R_i+R_{i−1}.                       (4)

## The triangular summation

Let M=sup F−inf F. Subtract inf F so that 0≤R_i≤M and |D_i|≤M. Set w_i=max(0,m−|i|), so Σ w_i=m². Multiply (4) by w_i and sum. Two finite index shifts give

    (κ/16)m² + (1/2)Σ w_i |D_i|
      ≤ Σ (w_{i−1}−w_i) D_i + Σ (w_{i−1}+w_{i+1}−2w_i) R_i.

All sums have finite support; the zero weights at ±m require no progression outside the chosen grid. The absolute first difference is at most 1. Wherever w_i≥2, its contribution is absorbed by w_i |D_i|/2 on the left. The nonzero first differences at smaller weights occur only at i=−m+1,m−1,m, costing at most 3M in total. The second difference is +1 at ±m, −2 at zero and zero elsewhere, so its contribution is at most 2M. Thus κm²≤80M. Since m=⌊σ r/(16η)⌋, inequality (2) follows. Applying (2) to restrictions of any candidate bounded potential on the unshaved block gives the stated impossibility.

## A fixed fraction of the block must see large variation

Assume now that F is measurable. Fix any real c₀ and replace F by F−c₀. Choose a fixed interval J of positive length for the center t₀ and σ>0 such that all t₀+[-σ,σ], for t₀∈J, lie in one compact subset of the same initial regime. Thus m is common to all centers. At each t there, let I_t be the folded union of the two eroded intervals, and let V_t be the length of the subset where |f_t|>T, for a threshold T>0 to be chosen.

Here is an interior bound which does not average the sizes of any outliers. For a convex g with [x−2d,x+2d] inside its domain, if the total length of {|g|>T} is less than d/4 then |g(x)|≤3T. Indeed, among 0<y<d some y has both x−y and x+y outside the bad set (the excluded y have total length below d/2). Midpoint convexity gives g(x)≤T. There is also some y with x+y and x+2y both outside the bad set (excluded length below 3d/8), giving g(x)≥2g(x+y)−g(x+2y)≥−3T.

The folded points a(t)−e and v=z(t)−e−1/4 stay uniformly interior to I_t by the strict inequalities on the compact band. Fix d>0 so small that radius-2d intervals around these points and around v−d stay inside I_t. Call a height good if V_t<d/4. At a good height the previous bound controls |f_t(a−e)|, |f_t(v)| and |f_t(v−d)| by 3T. The antipodal progression gives R_i≤f_t(v), while convexity gives

    R_i ≥ f_t(v)+(f_t(v)−f_t(v−d))/(4d).

Thus |R_i| and |D_i| are bounded by K T at every good height, for a fixed K independent of the threshold, the height, and η.

Repeat the triangular summation with signed centered values. After absorbing the interior first differences, κm²/16 is bounded by the three exceptional |D_i| plus |R_{−m}|+2|R_0|+|R_m|. All terms involve at most six indices independent of t₀. Take T=κm²/(224K). If all the corresponding heights were good the right side would be at most 7KT, which is strictly smaller than κm²/16. Hence for every t₀∈J at least one of those finitely many translated heights is bad. Translation invariance implies that the set of bad heights in the fixed band has length at least |J|/6. Each has V_t≥d/4. Unfolding can only increase the measure, since overlap representatives have the same potential. The Haar area with |F−c₀|>T is therefore at least d|J|/24. Finally m is bounded below by a positive constant times 1/η. This proves the asserted fixed-mass estimate.

Integrating over the exceptional set gives the mean absolute deviation bound. For normalized area take c₀ to be the mean and apply Cauchy–Schwarz. Since the block area is at most one, its standard deviation has the same order lower bound. The explicit potential of SignedEndpoint.md supplies the matching upper order.

## Consequence for constant quadratic forms

In the same coordinates let a positive definite two-by-two matrix Q give a pointwise endpoint cost ΔᵀQΔ in the prescribed real lifts. In the antipodal progression the height difference is zero, so the preceding proofs apply with κ=Q_aa: elsewhere they only use nonnegative costs. In particular σ_F≥c Q_aa/η² for the standard deviation under the uniform block law.

A fixed interior rectangle in one sheet also supplies a positive-area family of ordinary vertical progressions, uniformly in small η. Specifically translate every midpoint of a fixed smaller rectangle by ±d₀/2 in height, keeping the angle unchanged; choose d₀>0 so that the three rectangles lie in the first one. Every such second difference is at least d₀² Q_ss. Subtract the mean of F, integrate over the smaller rectangle and apply the triangle inequality followed by Cauchy–Schwarz. This gives Q_ss≤C σ_F. Consequently

    sqrt(det Q)/σ_F ≤ sqrt(Q_ss Q_aa)/σ_F ≤ C η.

The diagonal form and potential in SignedEndpoint.md attain this order. Thus changing the potential or using its actual standard deviation cannot improve the order of this determinant-to-standard-deviation ratio on these same eroded blocks. The conclusion addresses the covariance estimate used in the product-shell argument; a sharper method of finding an occupied shell can use information beyond standard deviation.

## Verification and sources

The finite summation inequality for signed centered values, the bound κ Σ w≤80M, and the single-height inequality (3) are checked in PotentialBarrier.lean. The local geometry and all-height sharpness conclusion are ordinary proofs above. The companion Fraction script tests the two actual progressions and both triangular-weight identities at six grid lengths up to 513 heights for the rational signed benchmark.

- Signed profile and optimal parameters: https://github.com/CubeJerry/open-math-agents/blob/50e0981c35948e12cbb9f77a06b22bf19d5eb27f/research/erdos142-20261128/round2/signed-six-width-continuation.md
- Quantitative upper construction for the necessary oscillation and the resulting integer lower bound: https://github.com/Deldor14/open-math-agents/blob/8780d565fc5a2e3061cb82809a3b6d3349453ddc/research/erdos142-hinge/SignedEndpoint.md
