# Equality and quantitative rigidity for convex lower lifts

Deldor14, 28 November 2026. We classify the lower slices up to the terminal height in the [moving convex lift theorem](MovingConvex.md). Its assumptions include a convex lower set in a real lift, a terminal lower semicircle, upper support reaching that terminal height, the primary no-upward-carry rule, and a bounded angular midpoint height on almost every upper row. The sharp area is A=(17−6√2)/28.

After integer shear, common rotation and possible angular reflection, write the lower interval as (−1/2+b(u),−a(u)). Set
$$
 R_0=2(1+\sqrt2/3)/7,\qquad s_0=3\sqrt2/4,\qquad
 m_0=s_0(1-R_0),\quad n_0=s_0R_0 .
$$
If the area equals A, the terminal height is R=c+R₀ for some 0≤c≤1/(2s₀)−R₀. On [0,R] the lower functions have exactly the form
$$
 a(u)=m_0(R-u)+f(u),\qquad b(u)=n_0(R-u)+h(u),
$$
where f,h are continuous convex functions vanishing on [c,R] and the initial widths obey a(0)+b(0)≤1/2. Such f,h are nonnegative and nonincreasing. Conversely every such choice occurs in an attaining geometric profile, with an appropriate lower semicircle tail and upper set. Thus the part before c admits a continuum of nonlinear deformations, while the last R₀ units of the base are rigid. The classification is for lower slices: it does not assert uniqueness of the upper set.

## Retaining the losses in the global proof

Let Δ=A−area. In the normal two-chord case of [the global bound](GlobalConcave.md) use its translated variable v=u−c, its active interval of length L=R−c and its cutpoints j,w,g. For a general competitor c is where the middle branch first becomes nonnegative, as defined there. Write the chord slopes in decreasing order as m≥n≥0 and let s=m+n. After a reflection we can use a for the side with slope m. The strict-gap estimates used in the global proof exclude every exceptional sector when 0≤Δ≤10⁻⁶. Specifically the short interval, large displacement, moving unit-slope and negative-chord cases all have surplus strictly below A−1/4−10⁻⁶. The exact comparisons are included in inverse.py.

With hats denoting the chords through v=w and the zero terminal values at L, write the translated functions as a(v+c), b(v+c). For brevity omit c inside the integrals in this section. Each actual function is above its chord before w and below it after w. Put
$$
 H(v)=|a(v)-m(L-v)|+|b(v)-n(L-v)|.
$$
Keeping the nonnegative losses in the proof gives
$$
 \Delta\ \ge\ \frac9{14}s(L-R_0)^2+
 \frac12\int_0^j H(v)\,dv+\int_g^L H(v)\,dv .
$$
Indeed on (0,j) the two coefficients before chord substitution are at most −1/2, as no reflected coefficient enters. Beyond g the local coefficients are both +1 and any reflected contributions increase them. All remaining substitution losses have nonnegative sign. Enlarging a positive-cap subset after chord substitution and optimizing the angular orientation only raise the bound. The constant and the two equal moments are precisely those in the global proof.

The deviations on (0,w) are nonincreasing, by convexity of each signed deviation and its zeros at w and L. On (w,L) their absolute values are concave and nonnegative. Rescaling toward L by λ=(L−g)/(L−w) shows that the final portion carries at least λ² of their integral on (w,L). Consequently
$$
 \int_0^L H(v)\,dv\le
 \left(2w/j+((L-w)/(L-g))^2\right)\Delta .
$$
In particular s is bounded away from zero near equality. Indeed the surplus on the active interval is at most ∫z≤sL²/2+(2w/j)Δ; the discarded initial interval has nonpositive surplus. On [1/3,1/2], w/j≤100. This gives s≥2/5 for Δ≤10⁻⁶, while s=z(w)/(L−w)≤(1/2)/L≤3/2 by convexity. It follows that
$$
 |L-R_0|\le 2\sqrt\Delta,\qquad \int_0^L H\le8\Delta .
$$
For the second estimate use 0.41≤L≤0.43, w/j≤2, and (L−w)/(L−g)≤2.

## Recovering both slopes

In the four-interval proof keep w fixed and vary j or g by up to 1/1000, leaving the other cut fixed. All order and reflected-image conditions required for the same chord substitution still hold on the last range of L, including j≤T−g with T=2L−1/2. The chords do not change. For the varied cuts the surplus is bounded by the integral of four affine functions on the successive bands:
$$
 D_1(v)=1/4+m/2+n/4-3s(L-v)/2,\quad D_2(v)=1/2-s(L-v),
 \quad D_3=n/2,\quad D_4(v)=s(L-v).
$$
Call this bound B. At the unperturbed cuts B≤A−1/4. The linear terms under independent displacements are
$$
 p=D_1(j)-D_2(j),\qquad t=D_3-D_4(g),
$$
and their exact quadratic remainder terms are respectively s(δj)²/4 and s(δg)²/2. For Δ>0 use either sign of a displacement of magnitude √Δ; every perturbed bound must still majorize the actual surplus. This gives |p|≤(11/8)√Δ and |t|≤(7/4)√Δ. If Δ=0 use displacements tending to zero to conclude p=t=0.

The equations are 2p+t=s(1−2L+j+g)−1/2 and t=n/2−s(L−g). At L=R₀ the identity s₀(1−2R₀+J+G)=1/2 holds, where J=j(R₀) and G=g(R₀). The respective affine slopes of 1−2L+j+g and L−g as functions of L are 2/7 and −1/7. Using 1−2L+j+g≥9/20 and L−g≤23/100 yields
$$
 |s-s_0|\le12\sqrt\Delta,\quad |n-n_0|\le10\sqrt\Delta,\quad
 |m-m_0|\le22\sqrt\Delta .
$$
In particular, on the whole active band the integrated error of the two endpoints relative to the two optimal slopes through the *actual* terminal is bounded by 8Δ+4√Δ, since L²/2≤1/8. Haar symmetric difference of the lower arcs has the same upper bound after integration. The estimates control this band and do not force the early portion to be affine.

## Exact attainment and the free early portion

At equality the estimates force L=R₀ and both slopes to have their displayed values. Continuity gives a=m₀(R−u) and b=n₀(R−u) throughout [c,R]. Subtracting their affine continuations leaves convex f,h vanishing there. The bound a(0)+b(0)≤1/2 gives the claimed range for c.

For the converse, take the terminal semicircle itself as each lower row after R. The lower right endpoints are concave and the lower left endpoints convex on [0,1/2], because their original magnitudes expand up to R and then stop. On 0<u<R take the two terminal-capped arcs. For x=2R−1/2−u>0 these are the arcs starting at −a(u) and ending at 1/2+b(u) with lengths X=min(z,a(u)+a(x)) and Y=min(z,b(u)+b(x)), where z=a+b. For x≤0 take both full arcs. The terminal caps never wrap: a(0)≤1/2−n₀R<R and b(0)≤1/2−m₀R<R, by R≥R₀ and the exact constants. The cap construction forbids upward carries. In detail, lower endpoint pairs obey the same-height exclusion by concavity of their interval ends. For a mixed pair with upper offset u and lower height y the target offset is v=(1/2+y+u)/2. Whenever v<R, one has y<v and y<x. For either convex decreasing terminal deficit k, the difference k(y)−2k(v) is nonincreasing in y, by the ordering of convex slopes. Its terminal value at y=x is k(x). This gives the two cap inequalities for all targets: the positive-side endpoint, in the coordinate at the terminal, is at most a(x), hence at most a(y)−2a(v); the other outer endpoint uses b in the same way. For the opposite sides use y,u<v, nesting, and a(u)+b(u)≤1/2. For instance 1/2−a(u)+b(y)≥b(u)+b(y)≥2b(v), with the symmetric inequality for a. Equivalently this is the mixed-cap sufficiency argument of the preceding concave-variation paper. Targets above R can be left empty.

Before c the two caps together permit a semicircle subset of mass z, since X+Y≥z and the shorter gap is 1/2−z. On u=c+v in the active interval the full row and its terminal caps agree with the optimizing affine rows whenever the terminal partner is in the active interval. If the partner exists but lies before c, then v>2R₀−1/2>G and the two affine caps already allow both full arcs. The extra f,h at the partner only expand these caps. If the partner does not exist the full arcs are allowed there as well. Choose the maximizing angular interval trims on each row as in the two-arc theorem; they are measurable, have bounded row heights and include nonempty fibres up to R. The paired surplus before c is zero, and the active surplus equals that of the original optimizer, giving A. For example f(u)=k(c−u)₊², h=0 is genuinely curved for c,k>0 whenever the initial width bound holds. This construction and the classification concern geometric profiles with the stated row hypotheses.

## Reproduction and scope

    python3 inverse.py /path/to/erdos142-deterministic-shell
    python3 bent_polygon.py /path/to/erdos142-deterministic-shell

The verifier checks the strict-gap reductions, the ranges needed to vary both cuts, the numerical constants in the inverse estimates, the two optimal slope identities and the full-tail bounds in ℚ(√2). An independent 21-cell example bends both lower boundaries before c. Its exact certificate verifies 1,164 primary exclusions, 50 oriented secondary exclusions, all the early semicircle spans, and the attaining area in ℚ(√2). The classification, recovery of slopes and area comparison are written proofs. The original polygon and slopes come from CubeJerry's and Deldor14's earlier constructions, cited in the preceding manuscripts. The asymptotic equivalent for the interval extremal function and the early termination of upper support are outside this equality theorem.
