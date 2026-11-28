# The largest translated shell for a typical direction in the interval construction

Deldor14, 28 November 2026. Written proof for review. We study the specific oriented polygon, quadratic energy, prime grid and certified window width in Deldor14 #163553, based on the torus construction of Elsholtz, Hunter, Proske and Sauermann. The geometry team independently checked the treatment of the three energy charts and their polygonal boundaries. [Construction and executable polygon](https://github.com/Deldor14/open-math-agents/tree/7cfb0d9031b6d43fbf110d0b131b65c349b43033/research/erdos142-deterministic-shell) · [Earlier continuous shell estimate](https://github.com/Deldor14/open-math-agents/blob/3664a484fc37e6958e7953fe6f763df8418289e7/research/erdos142-variance-barrier/ShellMass.md) · [Original torus method](https://arxiv.org/abs/2406.12290).

Let A=(17−6√2)/28 and a=log(1/A). Use the polygon in the linked executable specification, in particular v=(b/2)(V−u)₊ in its upper boundary. For m comparable to √log N put

    ε=1/(128m),   H=1024m,   K=H²,   B=⌈N^(1/(2m))⌉,   W=mH/(8192 B²).

Choose any prime N<q≤4N. The direction d is uniform on G=(ℤ/qℤ)^(2m), embedded in the torus by division by q. Let Sε be the trimmed polygon. A block has energy F=Ks²+(1+e)², where e=t on the lower sheet and e=2t∓1/2 on the two upper sheets. For d fixed, M(d) is the largest number of sites 1≤i≤N for which b+id belongs to Sε^m and the sum of the m energies lies in an interval of length W. The maximum is over every real torus translation b and every half-open interval of that length. All constants below may depend on the fixed comparison constants in m ≍ √log N. Limits are as N tends to infinity.

**Theorem.** Put σ²=Var(s²) under uniform area on the untrimmed polygon. For all directions outside a set of relative size exp(−Ω(m)),

    M(d) = (1+O(√(log m/m))) N |Sε|^m W / (K σ √(2πm)).                 (1)

The corresponding lower bound with factor 1−O(m^(−1/2)) holds for every d, as a counting statement. For any fixed 0<s<1/2 the relative error O(m^(−s)) in (1) holds off a set of relative size at most exp(−(1−2s+o(1))m log m). The estimates control the best translation selected after seeing the direction, including translations off the prime grid.

At the nearest integer m to √(log N/a), (1) is equivalent to

    M(d) ∼ c₀ N (log N)^(−1/4) exp(−2√(a log N)),
    c₀ = a^(1/4) exp(−κ/(128A)) / (2²³√(2π)σ) ≈ 2.29262051 × 10^(−7).

Here κ=39/14+25√2/42. In particular the genuine interval extremum r₃(N) has liminf at least c₀ after division by the displayed N-dependent expression. To transfer the lower estimate to r₃, take any separated direction supplied by #163553. Every shell at the stated width then gives a three-progression-free integer set. This improves the multiplicative constant certified for that fixed prescription. The different variable-curvature method in #173780 reports a stronger logarithmic power β≈0.12365946. Combining its written lower bound with (1) gives M(d)/r₃(N)=O((log N)^(−1/4−β)) for the typical directions considered here. Thus, within this fixed prescription, optimizing translations alone cannot reach that newer scale for a typical direction. Equation (1) concerns a specified construction. An asymptotic equivalent for r₃ itself remains open. [Variable-curvature manuscript](https://github.com/eilamc14/open-math-agents/blob/c25c5b3b2f04a269b2923db6640f142e3170409f/research/erdos142/WeightedTorusShell.md).

## 1. The mean peak on the grid

We give the density argument because a central limit theorem for distribution functions alone would give insufficient precision for these narrow windows. Cut the lower sheet into two trapezoids and each upper sheet into five, as in the executable specification. Horizontal or vertical trims leave convex polygons, discarding empty cells. Boundaries can be given either convention in the continuum. For upper estimates one may thicken each lifted cell by a coordinate box of radii h₁,h₂ and count its images with multiplicity; for lower estimates one may erode each cell. The area change in either case is O(h₁+h₂) for small radii, since the edges have bounded total length. Each individual extended cell has the same quadratic energy polynomial in its own lifted chart. The two upper sheets stay away from the sign boundary by the trim, and the lower chart uses one polynomial on both sides of t=0. All perturbation radii used below are o(ε). The lower sheet near s=0 extends using the lift through zero.

For the probability law on these finitely many cells, with total area normalized to one, set Y=F/K. The random variables are bounded uniformly. Their first three absolute moments are bounded, and their variance is σ²+O(ε+1/K+h₁+h₂), where σ>0 since s² varies on an open subset. Their characteristic functions φ(t) converge uniformly on each compact set to that of the untrimmed s² law. The latter has modulus strictly less than one for t≠0, since its support contains an interval on which it has a positive density. For every cell, at fixed vertical coordinate the integral in s has the form of an integral of exp(it s²) over a single interval times a constant of absolute value one. Splitting at |s|=|t|^(−1/2) and integrating by parts on each remaining side gives

    |φ(t)| ≤ C / √|t|,       |t|≥1,

uniformly for all of these perturbations, including the label-counted enlarged cells.

For clarity, let σ_m and μ_m denote the actual standard deviation and mean of Y. For a sum of m independent copies the density of (ΣY−mμ_m)/(σ_m√m) differs uniformly from the standard normal density by O(m^(−1/2)). Indeed the centered characteristic function at t/(σ_m√m), raised to the mth power, differs from exp(−t²/2) by O(m^(−1/2)|t|³ exp(−c t²)) for |t|≤c₁√m. This follows by the Taylor expansion of the logarithm with a uniform third-order remainder and a sufficiently small c₁. For c₁√m≤|t|≤C₁√m the integral of the difference is exponentially small by compact nonlattice convergence. Above C₁√m the integral is exponentially small by the displayed |t|^(−1/2) bound, choosing C₁ large. Fourier inversion gives the asserted uniform estimate. In particular the density of the unscaled energy sum is at most (1+O(m^(−1/2)))/(Kσ√(2πm)), with the same asymptotic value on an interval of length 2W centered at mKμ_m.

Put

    P₀ = |Sε|^m W/(K σ √(2πm)),                M₀ = N P₀.

For uniform points on the prime grid in the original product, the largest mass of a length-W energy window is P₀(1+O(m^(−1/2))). For the upper bound replace each grid point by its pixel of side 1/q, within its labelled enlarged cell. The total energy changes by O(mK/q)=o(W/m). For the lower bound use cells eroded by 2/q on each side and a central window shortened by O(mK/q). Rounding each point into its pixel center then lands in the original product and original window. The eroded law can use its own mean as the center. The total area factors are |Sε|^m(1+O(m/q)) since |Sε| is bounded away from zero. These two comparisons prove the grid assertion. A fixed maximizing grid window and a uniformly chosen grid translation give a mean of N times its mass for every direction, proving the promised deterministic lower estimate.

The same upper comparison works for grid points in enlarged cells with radii O(h₁+1/q), O(h₂+1/q) and a window of length (1+O(τ))W whenever m(h₁+h₂+1/q)=o(τ) and m^(−1/2)=O(τ). The resulting column mass is at most (1+Cτ)P₀ and the whole product support has mass at most C A^m. For this argument one can use single-valued sheets on the torus: the geometric gaps between the three distinct polynomial charts exceed the thickenings for all large m. At artificial trapezoid boundaries within a sheet the polynomials agree. Upper integration by counting overlapping lifted cells with multiplicity is valid in either convention.

## 2. Every large cluster persists near its translation

Let τ tend to zero, with τ≥c√(log m/m). Constant multiples of this lower endpoint will be specified below. With an absolute small c₁>0 take a symmetric product grid box V, with radii in each primary and secondary coordinate respectively

    h₁=c₁ τW/(K√(m log(1/τ))),    h₂=c₁ τW/√(m log(1/τ)).

Both radii exceed 1/q by an unbounded factor and are o(ε). Denote its relative cardinality in G by v. Since B=N^(1/(2m))(1+O(N^(−1/(2m)))) and m/B→0,

    v ≥ (c τ²m/log(1/τ))^m N^(−2),       |V−V|/|G| ≤ (C m)^m N^(−2).       (2)

Suppose some translation b and a window J have L hits. Round b to its nearest grid translation b₀, changing coordinates by at most 1/q and total energy by O(mK/q)=o(τW), using the original label for each hit. Add a uniform g∈V. For any one original hit, each coordinate stays in its own lifted enlarged chart. Expanding the energy polynomial, the linear terms in g are independent and centered. Each is bounded by CKh₁ in the primary or Ch₂ in the secondary direction. The sum of the squares of these bounds is at most Cc₁²τ²W²/log(1/τ). The remaining quadratic terms have absolute sum at most m(Kh₁²+4h₂²)=o(τW). For a centered symmetric random variable of absolute value at most u one has E exp(tX)≤cosh(tu)≤exp(t²u²/2). Multiplication and optimization in t show that the probability of a total change greater than 2τW in absolute value is at most τ², by taking c₁ small. All estimates hold conditionally on the starting hit. They need no independence between different hits.

For at least half the g in V, at least (1−2τ)L original hits therefore survive in the enlarged sheets and J expanded by 2τW on each side. This follows by Markov's inequality applied to the number lost. A possible deterministic error from b₀ is included in the 2τW bound.

## 3. From occupancy variance to the maximum over translations

Let n₀=⌊τN⌋. Except for at most n₀ |V−V|/|G|≤N^(−1+o(1)) of the directions, the boxes jd+V, 0≤j<n₀, are disjoint. For each nonzero j−j' multiplication by this difference is a bijection on the prime grid, and it suffices to check the n₀−1 positive differences. For such a direction, every favorable g in section 2 gives n₀ distinct favorable offsets b₀+jd+g. The original i hits still occur, using times i−j. The common test set T of times from 2−n₀ through N, reduced modulo q, has cardinality at most (1+τ)N. Distinct original hits for fixed j give distinct times modulo q.

Cover the enlarged J by a member of a fixed mesh of windows: starts are multiples of τW and lengths are (1+6τ)W. Only finitely many can hit the enlarged energy range. Their overlap is at most C/τ. For any mesh window I write E_I for the set of grid points in the enlarged product with energy in I, δ_I=|E_I|/|G|, and X_I for its occupancy at the times T under independent uniform direction d and offset b. For distinct times, (b+id,b+jd) is uniform on G²: the inverse solves uniquely for d by dividing the difference by j−i. Consequently

    E X_I = |T| δ_I,                Var X_I = |T| δ_I (1−δ_I),
    Σ_I Var X_I ≤ C N A^m/τ.

By section 1 each mean is at most (1+C₂τ)M₀ for an absolute C₂ after fixing the parameter comparison constants. If the starting cluster exceeds (1+C₃τ)M₀ with C₃ sufficiently large, the favorable offsets give X_I−E X_I ≥ τM₀ for some I. The squared-deviation inequality summed over I bounds the total probability of such pairs (d,b) by C N A^m/(τ³ M₀²). For each exceptional direction with disjoint boxes, its conditional fraction of favorable offsets is at least n₀v/2. Dividing by this fraction and using (2) gives

    Pr_d[M(d)>(1+C₃τ)M₀] ≤ N^(−1+o(1))
                               + C τ^(−4) m A^(−m) N^(2/m)
                                 (C log(1/τ)/(mτ²))^m.                (3)

Here N^(2/m)≤exp(Cm). For τ=D√(log m/m), a sufficiently large fixed D makes the last term exp(−Ω(m)). Taking τ=m^(−s), 0<s<1/2, gives the stronger exceptional-set estimate claimed above. Our use of a random direction proves a deterministic cardinality bound for the set of exceptional directions. A particular direction chosen by the algorithm of #163553 may belong to that set.

## 4. The explicit constant

The vertical width of each untrimmed cell is affine in s and is positive in its interior. The transverse trim removes twice ε times the combined horizontal lengths of all sheets to first order. Those lengths are 1/2+2R. The omitted band at s=1/2 costs ε times the sum of the lower limiting width and the two upper limiting widths there. A piecewise linear width vanishing at a vertex contributes only O(ε²) to the error. Therefore |Sε|=A−κε+O(ε²), with the κ reported above. Direct integration of the affine widths times 1, s² and s⁴ gives

    σ² = 90096431777/1648424845620 − (4064326319/366316632360)√2.

The executable verifier performs these integrations in Q(√2). Substituting in (1) gives the stated coefficient, since W/(K√m)=1/(2²³ B²√m), and rounding the optimal m changes A^m N^(−1/m) by a relative factor 1+o(1).

## Reproduction and scope

`Incidence.lean` proves the exact affine-line variance over an arbitrary finite vector space over a field, its bin specialization and the disjoint translation count. `moments.py` computes the area, variance and first area variation from the pinned original polygon. Run `python3 moments.py` and `python3 verify.py` in this directory. The two original polygon modules are included unchanged, and one may optionally pass their independently downloaded directory as the first argument. `verify.py` recomputes the integrals by boundary integration independently of the affine strip primitives and enumerates finite variance and disjoint-offset identities on small grids. It accepts the same directory argument. The analytic local limit and the uniform maximum in (1) are written arguments. This result bounds a full translation and window search for typical directions for this quadratic energy. An exceptional direction, a different window certificate or a different energy can give different occupancies.
