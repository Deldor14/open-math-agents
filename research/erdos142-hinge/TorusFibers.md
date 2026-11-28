# Which pairs of angular arcs admit a bounded midpoint potential?

The torus construction for three-term-progression-free sets uses a bounded function whose endpoint sum exceeds twice its value at a modular midpoint by a quadratic distance cost. We give a necessary and sufficient condition at one height for a pair of arcs in opposite semicircles. We also determine the best integral in a specified piecewise-affine grid with four height cells and all four local alternatives. This determines which geometric changes are worth exploring within that grid. The limiting density of the known continuous family is higher than the grid optimum. The asymptotic formula for the Roth number is open.

## The fixed-height criterion

Write the circle as ℝ/ℤ with the shortest circular distance d. Let I=(i₋,i₊) and J=(j₋,j₊) be nonempty real intervals inside (−1/2,0), allowing their boundary values to equal −1/2 or 0. Set B=(I+1/2)∪J in the circle. Write l=min(i₋,j₋) and z=max(i₊,j₊). The following are equivalent.

1. Some bounded real F on B satisfies F(x)+F(z′)−2F(y) ≥ d(x,z′)² for all x,z′,y∈B with x+z′=2y in the circle, including triples with equal endpoints.
2. At least one of the following four inequalities holds.

| Mode | Condition |
|---|---|
| A | i₊+j₊−2l ≤ 1/2 |
| B | 2z−i₋−j₋ ≤ 1/2 |
| D | i₊ ≤ j₋ |
| F | j₊ ≤ i₋ |

An empty physical arc can be handled directly by a quadratic on the other arc. The equivalence above classifies two nonempty physical arcs.

**Sufficiency.** In D, the arcs in their original lifts lie in an interval of length at most 1/2. In F, translate J by 1 for the same conclusion. Modular midpoints in either open semicircle are ordinary real midpoints in its lift. Twice the square of that real coordinate pays the required squared distance.

For A, write u for the folded coordinate in I or J and take F=4u². With endpoints on the same sheet the folded discrepancy u₁+u₂−2u_y is 0. With opposite endpoint labels it is ±1/2. The open endpoints and A exclude +1/2. When it equals −1/2, set m=(u₁+u₂)/2. Then u_y=m+1/4<0, so
[
 u_1^2+u_2^2-2u_y^2=(u_1-u_2)^2/2-m-1/8>1/8 .
]
This pays the distance cost since d≤1/2. For equal labels the ordinary quadratic identity pays the cost directly. Angular reflection interchanges A and B by replacing both folded coordinates by −1/2−u and interchanging the sheet labels. This gives the certificate for B.

**Necessity.** If D and F both fail, I and J overlap on an open interval. At each point of overlap the two representatives have the same F-value. Indeed, either is a modular midpoint when both endpoints equal the other representative. Applying the inequality both ways gives equality. Thus F defines a bounded function f on the entire folded interval (l,z). Its restriction to each original interval is midpoint-convex and hence convex by boundedness. Those restrictions agree on their open overlap, so f is convex throughout (l,z). Its one-sided endpoint limits are finite by boundedness, and their maximum H bounds f everywhere.

If A fails, then 2l+1/2 lies strictly inside I+J. The upper inequality is failure of A. For the lower inequality observe that i₋+j₋−2l=|i₋−j₋|<1/2 because both intervals are nonempty. Choose interior u∈I and v∈J with u+v=2l+1/2. For any sufficiently small ε>0, take folded endpoints u+ε, v+ε on the opposite labels, and target l+ε on a sheet starting at l. Their folded discrepancy is +1/2. These are actual modular progressions with the same strictly positive physical endpoint distance d₀ for all ε. Positivity follows because points in the interiors of the opposite physical semicircles are distinct. Thus 2f(l+ε) ≤ 2H−d₀². Taking ε down to zero gives f(l+)<H.

Likewise, failure of B puts 2z−1/2 strictly inside I+J. Here the other strict inequality is 2z−i₊−j₊=|i₊−j₊|<1/2. Choose interior endpoints with that sum, translate both by −ε, and target z−ε. The discrepancy is −1/2 and the physical endpoint distance is again fixed and positive. Hence f(z−)<H. Both strict conclusions together contradict the definition of H. This proves necessity for arbitrary bounded potentials, without a continuity hypothesis on the original physical arcs.

For example, I=(−1/2,−13/50), J=(−6/25,0) satisfy D and fail A and B. The usual one-sided folded-square test misses this fiber. A change of lift supplies its potential.

## A finite grid with all four alternatives

Use CubeJerry's signed coordinates for the lower and upper angular slices. The lower interval is (−L/2,W/2). The folded upper intervals are I=((−1−V)/4,(−1+P)/4) and J=((−1−M)/4,(−1+U)/4). In terms of widths the four alternatives are

| Mode | Width inequalities |
|---|---|
| A | P+U+2 max(V,M) ≤ 2 |
| B | V+M+2 max(P,U) ≤ 2 |
| D | P+M ≤ 0 |
| F | U+V ≤ 0 |

Take lower height knots 0, 50/119, 1/2 and upper offset knots 0, 12/119, 19/119, 25/119, 50/119 (the actual upper heights are 1/2 plus their offsets). All width functions are affine within each open cell. Their one-sided limits at each interior knot are independent. Each upper cell is assigned one fixed row of the table. Seam heights are discarded. Impose signed caps |width|≤1, 0≤L+W≤1, P+V≥0, U+M≥0. Retain the original sufficient inequalities that exclude upward vertical midpoints. Put R=max(P,U), S=max(V,M). For lower endpoints a,b and t=(a+b)/2 require
[
 L(a)+L(b)+R(t)le1,qquad W(a)+W(b)+S(t)le1.
]
For lower endpoint a, upper endpoint offset b and t=1/4+(a+b)/2 require
[
 P(b)+2W(a)+2S(t)le1,qquad M(b)+2L(a)+2R(t)le1 .
]
These apply when the endpoint and target cells exist. For this model the exact maximum of the area before trimming is **579/1904 = 0.304096638655462…**. The 256 mode assignments include the usual fixed orientation, its reflection, changes of orientation and both ordinary semicircle cases. Additional knots, changes of mode inside cells, empty-arc exceptions to the listed inequalities and other vertical exclusion mechanisms are outside this finite statement.

**Verification.** Each trapezoid integral is linear in the width limits. After expanding the maxima, every two-height inequality is affine on a rectangle clipped by a diagonal strip. Its extrema occur among the rectangle corners and the intersections of the strip edges with the rectangle edges. The verifier constructs these vertices using rational arithmetic. Lower-bound feasibility and the objective value are checked against an explicit primal vector.

For each upper certificate let Ax≤b denote its rows, c its area weights and x its width limits. For any vector of nonnegative multipliers y the coordinate caps give
[
 c^Txle b^Ty+sum_i |c_i-(A^Ty)_i| .
]
Thirteen rational certificates check an upper bound of 579/1904. A wildcard drops the local row on its cell, so proving that relaxation suffices for every choice there. Physical reflection sends (L,W,P,U,V,M) to (W,L,M,V,U,P) and preserves the area and the pair constraints. It exchanges A and B and preserves D and F. The verifier enumerates all assignments and checks coverage, including reflected certificates. Verification uses Python's standard library and no optimization solver.

Run `python3 TorusFiberGrid.py` beside `TorusFiberCertificates.json`. The result is
```
256 mode assignments, 13 rational upper certificates, optimum 579/1904
```

The rational benchmark is already attained by the original orientation. The continuous signed profile has limiting area (17−6√2)/28 ≈ 0.30409709377719. This calculation establishes optimality only for the specified rational grid and certification rules. It gives no upper bound for the Roth number.

Sources for the geometry and the numerical benchmark are the [signed-width construction](https://github.com/CubeJerry/open-math-agents/blob/50e0981c35948e12cbb9f77a06b22bf19d5eb27f/research/erdos142-20261128/round2/signed-six-width-continuation.md) and the [earlier fixed-orientation grid calculation](https://github.com/CubeJerry/open-math-agents/blob/50e0981c35948e12cbb9f77a06b22bf19d5eb27f/research/erdos142-20261128/round2/nonuniform_signed_lp.py). The motivating torus approach appears in [Elsholtz, Hunter, Proske and Sauermann](https://arxiv.org/abs/2406.12290).
