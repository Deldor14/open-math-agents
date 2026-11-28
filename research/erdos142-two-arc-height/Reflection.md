# Exact capacity of two angular arcs for a bounded midpoint height

Deldor14, 28 November 2026. This concerns one angular row of the torus construction for the three-term variant of Erdős #142. The row formula below also closes the arbitrary-holes case for the fixed lower layer from note #175410. It supplies a restriction on geometric constructions. A matching upper bound for the interval extremal function remains open.

## Statement

Use normalized lengths on the circle of circumference one. Let E consist of two disjoint open arcs, each of length at most 1/2. Write a ≥ b for their lengths and h ≥ g for the lengths of the two complementary gaps, so a+b+g+h=1. A rotation and a reflection allow the cyclic lengths to be written a,g,b,h. Endpoints can be discarded in all measure statements. Set
$$
 L=\min\{2b,\ (a+b+g-h)_+,\ (a-h)_+ +(b-g)_+\},\qquad x_+=\max(x,0).
$$

Among measurable subsets U of E admitting a bounded real-valued function F with
$$
 F(x)+F(2y-x)-2F(y)\ \ge\ c\,\|2(x-(2y-x))\|^2
 \quad (x,y,2y-x\in U)
$$
for some c>0, the largest possible measure is **a+b−L/2**. Here the norm is distance to the nearest integer. The maximum is attained by at most one subinterval in each original arc. Equivalently,
$$
 \min_{s\in\mathbb T} (1_E*1_E)(s)=L .
$$
The same capacity holds when the midpoint inequality is required almost everywhere in the endpoint and midpoint variables and F is measurable. For the upper bound a nonnegative continuous cost of the endpoint difference with a null zero set suffices. The explicit attaining heights below are for the displayed quadratic cost.

## A reflection about a high midpoint

Let E and U be arbitrary measurable sets with U contained in E. Write M for the supremum of a bounded F on U, and ignore an empty or null U. For every y with F(y)>M−δ, the cost at x and 2y−x is at most 2δ on their common membership set. If the cost is φ(x−z), Haar measure gives
$$
 (1_U*1_U)(2y)\le |\{v:\varphi(v)\le 2\delta\}|
$$
since x ↦ 2x−2y preserves Haar measure. The right hand side tends to zero for a nonnegative cost with a null zero set. Passing from E to U deletes at most twice the hole measure in any reflected intersection. Thus
$$
 |U|\le |E|-\tfrac12\min_s(1_E*1_E)(s).
$$
Convolution here is continuous by continuity of translations in measure. In fact some limit point of twice the high midpoints is a zero of the self-convolution of U. Under an almost-everywhere inequality take the essential supremum and choose good midpoints by Fubini. The null set of endpoints above the essential supremum, and its reflection, may be discarded for each such middle.

There is also a quantitative version. For the quadratic cost suppose the right hand side in the statement is reduced by ε≥0, and the bound can fail for endpoints x in an additional set of measure at most η at each good middle. The map x ↦ 4(x−y) preserves Haar measure. The measure of its preimage at distance at most √((2δ+ε)/c) from an integer is at most twice that radius. Letting δ decrease to zero gives
$$
 |U|\le |E|-\tfrac12\min_s(1_E*1_E)(s)+\sqrt{\varepsilon/c}+\eta/2 .
$$

## Three attaining constructions

Keeping the larger arc loses b. A semicircle containing the shorter gap can retain at least min(a+b,1/2−g) of the two arcs. When the available length 1/2−g fits inside their total length, split it between adjacent portions of the two arcs. Otherwise the entire envelope fits. A real coordinate squared inside the open semicircle gives a bounded height with the required cost, since the only eligible midpoint there is the ordinary midpoint in the lift. Both constructions give subsets with one interval per original arc. For the semicircle it suffices to take the two adjacent portions explicitly.

For the third construction place the larger arc at (r,r+a) in the positive half and the smaller at (−l−b,−l) in the negative half, with r+l=g. This is possible as the admissible ranges for r and l are [0,1/2−a] and [0,1/2−b], whose total length is g+h. Choose the orientation so the designated gap is the shorter one. Set p=r, M=l+b, d=M−p and keep the positive and negative *magnitudes* in
$$
 (p,\min(r+a,(1-d)/2)),\qquad (\max(l,d/2), M).
$$
The loss is exactly ((a−h)₊+(b−g)₊)/2 by substitution. The cuts fit because p+M≤1 and d/2≤M. For mixed positive and negative endpoint magnitudes X,V, a negative middle of magnitude w could cause a negative signed-chart deficit only if V=X+2w, and a positive middle w only if 1+X=V+2w. The retained intervals preclude both equalities by their strict endpoints and the inequalities 2 inf(negative)≥M−p and 2 sup(positive)≤1+p−M. For same-sign endpoints the chart deficit is zero. Hence e(x)+e(z)≥2e(y) with e(t)=2t−sign(t)/2. The increasing convex function F(t)=(2+e(t))² gives a deficit at least (e(x)−e(z))²/2, which dominates the required torus cost for c=1/2. Choices supported on a single arc use the semicircle height. Together these constructions give occupancy at least a+b−L/2. They adapt the interval trims in the [oriented compression proof](https://github.com/Deldor14/open-math-agents/tree/7f415e1c2ca48ccce538afc90b0e939e7ed7563c/research/erdos142-fibre-compression).

## Finite polyhedral proof for all real arc parameters

It remains to prove that every shift has reflected overlap at least L. Here is the proof by exact vertex enumeration, implemented in two_intervals.py using only Python integers. Allow arbitrary circumference T=a+b+g+h and replace the half-turn by T/2. The formula for L is homogeneous. Use endpoints e=(0,a,a+g,a+g+b). As a function of shift s the periodized self-convolution is linear between the ten unordered endpoint sums taken modulo T. It suffices to check all ten traces s=eᵢ+eⱼ; the true minimum of an affine function on each interval is reached at an endpoint.

For each trace consider the normalized shape polytope T=1, a,b,g,h≥0, a≥b, h≥g, 2a≤T. The branch hyperplanes for overlap on the trace are s−eₖ−eₗ+jT=0, |j|≤2. Indeed each ordered arc pair contributes its real reflected intersection summed over those shifts. Other shifts have zero real overlap, apart from possible null endpoint contacts, since all sums lie between 0 and 2T. The real overlap is affine except when endpoints coincide. The target L is a continuous selection among
$$
 0,\quad 2b,\quad a+b+g-h,\quad a-h,\quad b-g,\quad a+b-g-h .
$$
Include all their pairwise equality planes. This collects every change in L, since the signs of a−h, b−g and a+b+g−h are then fixed as well. A plane that does not change sign over the original polytope can be omitted. On each resulting cell the difference between overlap and L is affine. It suffices to verify it at every vertex, including the boundary of the original polytope, by continuity.

In four homogeneous coordinates each such vertex is the normalized ray cut out by three independent planes, with the original facets included. Signed 3-by-3 minors generate its coordinates. Discard the zero vector and rays outside the domain. At each retained ray compute the actual interval intersection with min and max and compare it directly to L. The verifier checks 177 trace–vertex pairs, covering 26 distinct normalized shapes. These checks prove the claimed inequality on the full continuum. The reflection bound and the three attaining constructions then force equality, both in the capacity statement and in the convolution minimum.

## The fixed lower layer

Keep the exact lower fibres, the primary no-upward-carry condition and the terminal support hypothesis in the [fixed-chart paper](https://github.com/Deldor14/open-math-agents/tree/7f415e1c2ca48ccce538afc90b0e939e7ed7563c/research/erdos142-fibre-compression). Its primary-only argument traps the upper row at offset u in the physical envelope Eᵤ=(r,C) ∪ (−D,−l), up to endpoints, with r,l,C,D as specified in the accompanying README. Let W(u) denote the sum of the two upper widths in the original signed polygon. The independent special-purpose certificates reflect.py and vertices.py prove
$$
 (1_{E_u}*1_{E_u})(s)\ge 2(|E_u|-W(u))\qquad(0\le u\le R,\ s\in\mathbb T).
$$
The first partitions the endpoint-sum traces and uses 98 exact tests across ten height subintervals. The second evaluates the convolution as a signed sum of positive-part functions on a two-dimensional arrangement, including the rectangle boundaries. It finds 126 distinct vertices and equality at 41. Both use exact arithmetic in ℚ(√2). Thus every measurable upper row admitting the midpoint height has width at most W(u). Integration with the fixed lower layer gives exactly (17−6√2)/28, attained by the original polygon. No common angular chart or connectedness hypothesis on the competitor is needed. The primary exclusion and terminal assumption remain essential hypotheses of this deduction. Independent interval replacements above control one row at a time. Compatibility of arbitrary replacements across different primary coordinates would require a separate argument.

## Reproduction and attribution

Run in this directory, passing the directory of the two original polygon Python modules to the last two commands. The [original modules](https://github.com/Deldor14/open-math-agents/tree/0d8d57f4a3898285fe9db73305d898aa0a36b99f/research/erdos142-deterministic-shell) use the standard library.

    python3 two_intervals.py
    python3 reflect.py /path/to/erdos142-deterministic-shell
    python3 vertices.py /path/to/erdos142-deterministic-shell

The Deldor14 geometric and verification chats independently identified the high-midpoint reflection test. The verification chat supplied the independent vertices.py arrangement and the additive-error estimate with its Lean proof. The general two-arc capacity formula, its homogeneous certificate, and the fixed-profile trace certificate were developed in the geometric chat. This is a written proof with exact executable certificates. RobustReflection.lean proves the deletion inequality, the Haar small-cost bound, and the quantitative row deduction conditional on the envelope overlap bound. The polyhedral proof of that envelope bound is certified by the Python scripts. The three Lean declarations compile with Lean 4.33.1 and use only propext, Classical.choice and Quot.sound. The signed construction and earlier four-mode searches are attributed in the accompanying README.
