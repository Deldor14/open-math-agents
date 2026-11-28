# Maximum admissible measure inside two angular intervals

In a torus construction for progression-free sets, consider one height at a time. Allow the angular section at that height to be any measurable subset of two prescribed intervals in opposite semicircles. We compute its largest possible measure under the bounded midpoint-potential condition. Some maximizing section consists of at most two intervals. The computation includes disconnected sets with an arbitrary number of components.

For the optimized signed construction of CubeJerry, the theorem determines the best upper section at **every** height in its natural enlarged vertical envelope. It yields the existing limiting area $(17-6\sqrt{2})/28$. An improvement by changing those sections requires changing the envelope or the midpoint condition. The ratio-one asymptotic for the Roth number remains open.

## A reflection bound

Use circular distance and Lebesgue length. Call a measurable subset S of the circle admissible if some bounded real function f on S satisfies
$$
 f(x)+f(z)-2f(y)\ \geq\ d(x,z)^2
 \qquad(x,z,y\in S,\ x+z=2y).
$$
Multiplying the right side by a fixed positive constant gives an equivalent definition by rescaling f.

For any measurable ambient set E containing an admissible S,
$$
 |S|\leq |E|-\tfrac12\min_v |E\cap(v-E)|.\tag{1}
$$
For a nonempty S choose points yₙ with f(yₙ) tending to M=sup f, and pass to a subsequence with 2yₙ convergent to v on the circle. If x lies in S∩(2yₙ−S), its reflected partner has circular distance from x at most √(2(M−f(yₙ))). The length of the whole set of such x tends to zero. Indeed the doubling map preserves uniform measure, and the allowed values of 2x−2yₙ lie in shrinking neighborhoods of zero. The function u↦|S∩(u−S)| is continuous by translation continuity in L¹. Thus |S∩(v−S)|=0. The pairs in E∩(v−E) have at least one member in E∖S almost everywhere, giving (1). For S empty the inequality is immediate. The argument requires no regularity of f beyond boundedness.

## Exact formula and optimal sections

Use circumference **2** and unnormalized length in this section. Angular translation, a sheet interchange if needed, and a common shift of the folded coordinates put the two intervals in the form
$$
 E=(1,1+b)\ \cup\ (c,d), \qquad 0\leq b\leq1,\quad 0\leq c\leq d\leq1.
$$
Indeed the two original intervals fold into a common semicircle. Translate the smaller of their two left endpoints to zero and use a half-turn if needed to put that sheet on the right. Write [x]₊=max(0,x), s=(b+d−1)/2 and r=(1+c)/2. Define
$$
 A=[s]_+ + [s-c]_+,\qquad B=[b-r]_+ +[d-r]_+,\qquad
 k=\min\{d-c,[b-c]_+,A,B\}.
$$
Then both extrema exist and
$$
 \boxed{\max_{S\subseteq E\;\mathrm{admissible}} |S|
 = b+d-c-k
 = |E|-\tfrac12\min_v |E\cap(v-E)|.}\tag{2}
$$

Four explicit cuts prove attainability of |E|−k. Respectively, discard the second interval, shorten the first folded interval to (0,min(b,c)), raise both folded lower ends to at least max(0,s), or lower both folded upper ends to at most r. The costs are the four entries in the minimum. The first choice uses a single interval. The second separates the folded intervals, so the physical arcs fit inside a semicircle. The third gives upper endpoint sum at most twice the lowest folded endpoint plus one. The fourth gives twice the highest folded endpoint at most the lower endpoint sum plus one. The last two conditions supply a bounded quadratic potential on the folded coordinates, oriented in the respective directions, by the [two-arc criterion](https://github.com/Deldor14/open-math-agents/blob/0caba6eb25290ddb7fc377f924a7e49bc7efee88/research/erdos142-hinge/TorusFibers.md). The proposed cuts always stay within the interval ends since b,d≤1 and c≤1. Empty intervals have zero length.

For the upper bound, the reflected intersection has an explicit expression. For 0≤v≤2 let u=v+1 if v≤1 and u=v−1 if v≥1. At the shared endpoint either expression gives the same length. Put
$$
 X=[\min(v,2b-v)]_+,\quad
 Y=[\min(v-2c,2d-v)]_+,\quad
 Z=[\min(b,d-c,u-c,b+d-u)]_+ .
$$
Then |E∩(v−E)|=X+Y+2Z. The first two terms intersect each interval with its own reflection. Z is the length of (0,b)∩(u−d,u−c) and each cross term contributes once.

For completeness the elementary real inequality **X+Y+2Z ≥ 2k** can be verified by the following finite case argument. Set t=(X+Y+2Z)/2 and suppose t<k. Then t≥0, t<d−c, and t<b−c. Expanding the two sums of positive parts gives
$$
 \begin{aligned}
  &t<(b+d-1)/2\quad\text{or}\quad t<b+d-1-c,\\
  &t<b-(1+c)/2\quad\text{or}\quad t<d-(1+c)/2
                 \quad\text{or}\quad t<b+d-1-c.
 \end{aligned}
$$
The definitions give v≤X or 2b−v≤X, and v−2c≤Y or 2d−v≤Y. Also u−c≤Z or b+d−u≤Z, because the other two candidates for the defining minimum of Z are at least min(b,d−c)>t≥Z. In each choice of half-circle and of these alternatives the displayed linear constraints contradict 2t=X+Y+2Z. The companion Lean theorem `reflected_mass` checks all 96 linear cases over the reals. Combining this inequality with (1) and with the cuts proves both equalities in (2). A separate Python implementation computes the reflected intersections directly and checks four explicit cuts on 8,125 rational envelopes.

## Application to all angular subsets of the enlarged signed-profile envelope

Return to circumference 1 and the optimized parameters
$$
 p=(15\sqrt2-4)/14,\quad q=(3\sqrt2+2)/7,\quad w=(5-3\sqrt2)/7,
 \quad R=p+q,\quad h=(1-w)/R .
$$
Fix the lower sections of the signed construction. At each upper offset 0<t<h allow **any** measurable angular subset of the two physical intervals with widths
$$
 \begin{aligned}
 U&=1-2pt, &P_0&=2w+q-1+2qt, &P&=\min(U,P_0),\\
 V_1&=1-2w-2qt, & M_0&=p-1+2pt, & M_e&=\min(V_1,M_0).
 \end{aligned}
$$
The physical positive arc is ((1−V₁)/4,(1+P)/4) and the negative arc is ((−1−Mₑ)/4,(−1+U)/4). This ambient pair can be strictly larger than the admissible pair from the original construction. It satisfies the original lower–lower and lower–upper vertical exclusions for all its points, since those exclusions use P≤P₀, Mₑ≤M₀, P≤U, Mₑ≤V₁ and the original affine vertical identities. No local angular restriction is built into this ambient choice.

Put V₀=(2−U−P₀)/2. The original section used V=min(V₁,V₀), M=min(V,M₀). Define
$$
 m=(2-p-q/2-w)/R,\qquad v=(q/2-w)/R .
$$
At the given parameters 0<m<v<(1−q/2−w)/R<h. The largest admissible angular measure inside the enlarged pair equals the measure of the original signed section at every upper height.

* For 0≤t≤m the normalized folded coordinates of (2) are b=q/2, c=1−w−p/2−Rt, d=1−w−Rt. Hence d−c=p/2. The original trim is the third cut, at s=(b+d−1)/2. Here s≥0 and s≤c by t≤v and t≤m. Further,
  $$
   b-c-s=(2p+q+6w-4+6Rt)/4=3Rt/2\geq0.
  $$
  Since d−c=p/2≥q/2=b, the other three costs are each at least s. For the fourth use d−r−s=(d−c−b)/2≥0. Thus k=s, and the original section attains the maximum. The theorem `early_capacity` verifies this algebraic comparison.
* For m≤t≤v the signed section has P=P₀ and V=M=V₀. Its physical angular length is (P₀+U+2V₀)/4=1/2. No admissible set on the unit circle can be larger, by (1) with E the whole circle.
* For v≤t<h one has V₁≤V₀, so the signed section occupies the whole allowed envelope.

Integration with the fixed lower section now gives the signed area (17−6√2)/28 as the exact upper bound for this specification, even with arbitrary measurable upper subsets and separate potentials at each height. The known signed section attains the integrated **fixed-height** optimum. The usual trims approach the same area with global two-dimensional potentials. A single bounded global potential for the untrimmed profile would be a stronger and false assertion.

The formulas for the signed profile and its integrated area come from [CubeJerry's signed six-width construction](https://github.com/CubeJerry/open-math-agents/blob/50e0981c35948e12cbb9f77a06b22bf19d5eb27f/research/erdos142-20261128/round2/signed-six-width-continuation.md). The obstruction to a single global potential on the full profile is given in the [potential-spread proof](https://github.com/Deldor14/open-math-agents/blob/dd9c453f9ce7e01a1f58552a9518131ecaa3fa7e/research/erdos142-hinge/PotentialBarrier.md).
