# Angular weights after measurable deletions from the compulsory band

Deldor14, 28 November 2026. We treat the geometric construction for `Erdos142.erdos_142.variants.three`. The exact maximizing blocks of [Equality.md](Equality.md) have a compulsory pair of angular arcs on a primary strip, by [ForcedBand.md](ForcedBand.md). The estimate below allows arbitrary measurable deletions in those arcs, including deletions with empty-interior complement. Only their total area enters. The matching construction and interval lower bound are due to [zeemy23](https://github.com/zeemy23/open-math-agents/blob/8854e183a6466b5a14e166ab82e437ef7b500950/research/erdos142/torus-bound/LowerBound.md), following eilamc14's weighted shell and the signed polygon of CubeJerry and Deldor14.

## Statement

Use normalized primary and doubled-angular coordinates on the compulsory strip. At primary offset $0<u<J$ its positive and negative sheets have open $e$-intervals $(a,c),(p,d)$ from [the affine chart proof](https://github.com/Deldor14/open-math-agents/blob/09cc34d24f91f8cb7ee24bbb0d1fa927af172d04/research/erdos142-angular-flatness/README.md). Write $S$ for this strip in physical coordinates and $B_0=|S|=-4/49+9\sqrt2/98$. The normalizations may vary with the member of the sequence. Let $T_\varepsilon$ be a measurable torus domain, $|T_\varepsilon|\to A=(17-6\sqrt2)/28$, with a bounded Borel height of range $K=O(\varepsilon^{-2})$ and measurable $w\ge0$. Assume Jensen nonnegativity on every ordinary-primary progression and the additional lower bound $w(X)^2\|2(t_X-t_Z)\|^2$ on the energy defect of every same-primary progression with endpoints $X,Z$ and middle $Y$. These conditions survive the normalization, including integer shear for which only the same-row cost is needed. The upper band lies within an ordinary primary chart.

If $|S\setminus T_\varepsilon|\le \varepsilon^{\alpha-o(1)}$ for $0<\alpha\le1$, then
$$
 \limsup_{\varepsilon\downarrow0}
 \frac{\int_{T_\varepsilon}\log^+ w}{|T_\varepsilon|\log(1/\varepsilon)}
 \le 1-\alpha B_0/A .
$$
In particular deletion of $O(\varepsilon)$ area, or $O(\varepsilon\log^C(1/\varepsilon))$ for fixed $C$, preserves the sharp previous cap. No interval or regularity assumption is made on the deletions. The hypotheses on $T_\varepsilon$ outside the strip are just those in the statement. Knowing the area of an arbitrary near-maximizer alone does not establish this one-sided proximity to the strip.

## Finite angular comparisons

Work on compact primary intervals strictly inside $(0,J)$, leaving a fixed buffer. All constants can depend on those intervals and on the fixed positive margin of the tested angular endpoints from their sheet boundaries. Each sheet contributes physical measure $du\,de/2$. Subtract a constant so that the height takes values in $[0,K]$. The following chart identities and strict inequalities hold uniformly with interior margins on compact primary intervals:
$$
 a<p<c\le d,\qquad (a+p)/2<a+1/2<(c+d)/2,\qquad
 d=(a+p)/2+1/2,\qquad p'-a'=-2q,quad q=3\sqrt2/4.
$$
All four edges are affine on this open strip. Choose $r>0$ small, $h=2r/q$, and an angular translation $|\tau|<r/3$. Denote the shifted coordinates by
$$
 A_u=a(u)+r+\tau,\quad P_u=p(u)+r+\tau,\quad D_u=d(u)-r+\tau.
$$
Below $M(u)$ is the negative-sheet height at $D_u$ when present. For mixed angular charts we use the two torus midpoint identities from the cited proof: a mixed pair at average $A_u+1/2$ has a positive midpoint at $A_u$, while the mixed pair $A_{u-h},P_{u+h}$ has a negative midpoint at $D_u$ since its average plus $1/2$ is $D_u$.

Heights on the two sheets coincide almost everywhere on their common surviving projection. At a common density and approximate continuity point for the two restricted heights, take symmetric endpoints approaching it on the first sheet and use the point on the other sheet as midpoint. Jensen bounds the height on the latter by that on the first. Interchange the sheets. Symmetric endpoints exist since the two reflected sets of good small displacements both have density one at zero. Apply this argument row by row and use Fubini. Mark this planar null exceptional set as a hole on each sheet. At a comparison point request both copies whenever they are used.

Here is a row comparison requiring at most $C(1+k)$ probes, where $k=\lceil\log_2(2+K)\rceil$. For any nominal target $\xi$ in a compact interior portion of its designated sheet, the tested point has coordinate $\xi+\tau$. The probes before adding $\tau$ depend only on $u,r,\xi$ and the designated sheet. Whenever they all survive, they imply
$$
 F(P_u)\le M(u)+C,\qquad
 c_1 w(u,\xi+\tau)^2\le M(u)-F(A_u)+C
 \tag{1}
$$
for a uniform $c_1>0$. Here and below $A_u$ uses the positive sheet and $P_u$ the negative sheet.

To see this, use a mesh of a fixed number of equal subintervals on $[A_u,D_u]$. Its spacing is uniformly positive and can be made as small as desired relative to the compact margins and minimum sheet overlap. Every three successive mesh nodes then lie together on one sheet: near $A_u$ choose the positive sheet, near $D_u$ the negative sheet; in the interior the overlap supplies a fixed Lebesgue number. Choices may be made before adding $\tau$ and kept for all the indicated shifts, using the inward displacements at the extreme nodes. Comparisons on three successive nodes, and equality where a change of sheet is used, give a convex sequence $f_j$ of heights. Its piecewise affine interpolant is convex. Let $M_*=\max(F(A_u),M(u))$ and $L=M_*-\min_j f_j$. The gap from $M_*$ to the interpolant is nonnegative concave. On any fixed interior subinterval it is at least $\gamma L$ with $\gamma>0$, by the chords from a maximum gap to the two ends.

For an additional point inside a mesh cell its height is at most the linear interpolation of the cell endpoints plus $2^{-k}K\le1$ if $O(k)$ further probes survive. In normalized cell coordinates $s\in[0,1]$, bound its height by the average at $\lfloor2s\rfloor$ and $2s-\lfloor2s\rfloor$ for $s<1$, stopping at an endpoint. Iterate. The affine interpolant satisfies equality at each step and the final residual is at most $2^{-k}K$. Use one sheet containing the entire cell; if the test uses the other sheet at the point, include the equality probe there. Every orbit point receives the same additive translation $\tau$, including after any number of doublings, since the mesh endpoints themselves are translated.

Choose $x\in(a,c)$ and $z\in(p,d)$ with $(x+z)/2=a+1/2$, uniformly interior on the fixed primary buffer. For example interpolate simultaneously between $(a,p)$ and $(c,d)$. The shifted points $x+r+\tau,z+r+\tau$ give a mixed midpoint at $A_u$. They lie in a compact interior part of the entire mesh. Their interpolation upper bounds therefore imply
$$
 F(A_u)\le M_*-\gamma L+1 .
$$
If $M_*=F(A_u)$ this gives $L\le1/\gamma$ and $F(A_u)-M(u)\le L$. Otherwise $M_*=M(u)$ and $\gamma L\le M(u)-F(A_u)+1$. In both cases $M_*\le M(u)+C$ and $L\le C(M(u)-F(A_u)+C')$. Interpolation at $P_u$ proves the first part of (1).

For the second part choose a mesh node a distance between one and three mesh spacings from the target, with its reflection of the target across the node still interior to the target's sheet. This is possible uniformly by the compact margins and choosing the mesh fine enough, with the doubled-coordinate separation of the endpoints bounded strictly between zero and $1/2$. The two endpoints have height at most $M_*+1$ by interpolation and the middle mesh node has height at least $M_*-L$. The weighted inequality gives (1). This proof only uses its weight at the actual designated endpoint.

## Primary comparisons with missing probes

Whenever the required comparisons at $u-h$ and $u+h$ survive, the mixed progression through $D_u$ and (1) yield
$$
 \delta_h M(u)\ge c_1 w(u-h,\xi+\tau)^2-C,
 \qquad \delta_h M(u)=M(u-h)+M(u+h)-2M(u).
 \tag{2}
$$
At the right row only the first estimate in (1) is needed. Independently, $\delta_t M(v)\ge0$ for **every** step $t$ for which its three negative-sheet probes survive in the buffer: $D_v$ is affine in $v$, and these three points form an ordinary progression on the same sheet.

Fix a target primary interval $I$ and choose a small fixed $H>0$ with its $5H$ neighborhood inside the buffer. Take $n$ with $H/2<2^n h\le H$. For roots in the $2H$ neighborhood of $I$ start with $\delta_{2^nh}M$. Its value is between zero and $2K$ when the three probes survive. At a node of step $2t$ descend to centers shifted by $-t,0,t$ with probabilities $1/4,1/2,1/4$. Use the identity
$$
 \delta_{2t}M(v)=\delta_t M(v-t)+2\delta_t M(v)+\delta_t M(v+t).
$$
If all five probes exist, the three child quantities are nonnegative and the conditional mean is one quarter the parent. If some probe is missing, kill this path at that node. Set the contribution of paths started with missing root probes to zero as well. Discarding any branches at later levels can only decrease the sum of surviving curvatures. Iteration bounds the mean of $1_{\rm success}\delta_h M$ by $2K4^{-n}\le CKh^2$. Additional row probes at the leaf can be required at this stage because the surviving leaf curvature is nonnegative. All centers used are within the fixed buffer.

Let $D=|S\setminus T_\varepsilon|$. Integrate over the root in the indicated interval, nominal target angle in a fixed bounded range, and uniform $\tau\in(-r/3,r/3)$. Restrict angular targets to the compact sheet portions in (1). For every fixed path the leaf primary coordinate is the root plus a constant, the target row is one further shift by $-h$, and each tested row is the root plus a fixed offset. Every angular probe has the form $e_0+\tau$, with $e_0$ independent of $\tau$. Thus the integrated measure of failures for any one probe lying in the strip is at most $C D/r$, by first integrating in $\tau$ and then in the root, for each nominal target angle. There are at most $C(n+k+1)$ probes on **one path**, including the probes validating all three child signs at each descent. The probability bound uses a union only along this path and is unchanged by averaging paths. Restricting to valid nominal target ranges can only decrease the loss estimate. This counting does not request the exponentially many probes of the full tree simultaneously.

Markov's inequality in (2) now gives, on any fixed compact interior portion $Q$ of either sheet,
$$
 |\{X\in Q\cap T_\varepsilon:w(X)>W\}|
 \le C_Q\left(\frac{(1+\log(1/r)+\log(2+K))D}{r}
                   +\frac{1+Kr^2}{W^2}\right),\qquad W\ge1. \tag{3}
$$
Indeed for every fixed path and $\tau$ the change from (root, nominal angle) to (target row, actual angle) is a translation with Jacobian one in $du\,de$. Every target in $Q$ is covered, using a slightly larger compact portion for the nominal test and the chosen root buffer. The physical factor $1/2$ is absorbed into the constant. For the successful branches use (2) and the integrated mean curvature bound. For the killed branches use the union estimate above. This proves (3) also when entire primary rows are missing.

## Passage to logarithmic weights

Fix $0<\eta<\alpha$ and take $r=\varepsilon^{\alpha-\eta}$, $W=\varepsilon^{-(1-\alpha+2\eta)}$. The right side of (3) tends to zero. To convert convergence in measure to the integral bound, use the odd-grid tail estimate in [ForcedBand.md](ForcedBand.md): uniformly in each primary row,
$$
 \int\log^+\!\left(w/\max(1,\sqrt{2K})\right)\le C .
$$
It follows by sampling odd cyclic grids and summing the [Bloom–Sisask bound](https://arxiv.org/abs/2007.03528) on three-term-progression-free density. Thus even on an arbitrary set of area $o(1)$ the positive logarithm contributes $o(\log(1/\varepsilon))$. On $Q$ the remaining contribution is at most $|Q|(1-\alpha+2\eta)\log(1/\varepsilon)$. The rest of the domain contributes at most its area times $\log(1/\varepsilon)+O(1)$, with a further absolute additive constant from the tail. The missing portion of $Q$ has area tending to zero. Exhaust both open sheets of area $B_0$ by such compact portions and send $\eta$ to zero. This proves the statement.

For $D=O(\varepsilon)$ formula (3) gives the more quantitative local estimate $\int_{Q\cap T_\varepsilon}\log^+w=O_Q(1+\log\log(1/\varepsilon))$. Indeed set $L=\log(1/\varepsilon)$, $r=\varepsilon L^2$ and $W=L^3$. The exceptional area is $O_Q(1/L)$, whose logarithmic contribution is $O_Q(1)$ by the same tail estimate. The other points contribute at most $3|Q|\log L$. The constants depend on the interior buffer, so this quantitative refinement is local.

For $\alpha=1$, the angular mean and the associated power $0.1706764818636109\ldots$ in the weighted-shell normalization are already attained by zeemy23. The theorem is an obstruction to improving that mean through low-area deletions from the compulsory band. It gives no upper bound of this scale for $r_3(N)$ and leaves open different underlying domains, non-diagonal metrics, alternative extractions and the asymptotic equivalent.

## Reproduction

Run `python3 perforation_checks.py /path/to/erdos142-deterministic-shell`. The script verifies the primary tree inequality with exact integers on perforated grids, the dyadic interpolation identity with exact rationals, and the two mixed midpoint coordinates and mesh geometry using the original polygon arithmetic. These are finite checks of proof ingredients. The measure estimates and the theorem above are written proofs.

The file `PrunedCurvature.lean` proves the subdivision identity and the pruned-tree bound `retained_le` on arbitrary subsets of the integer line and all dyadic depths. The latter controls the unnormalized leaf sum, which is the path expectation multiplied by $4^n$. This uses only nonnegative second differences on surviving stencils. The two declarations compile with Lean 4.33.1 and Mathlib with axioms propext, Classical.choice and Quot.sound.
