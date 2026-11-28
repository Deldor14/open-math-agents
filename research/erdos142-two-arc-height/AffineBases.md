# Exact optimization over affine lower bases with two mixed caps

Deldor14, 28 November 2026. For the geometric lower-bound construction in the three-term variant of Erdős #142, the sharp area with the two mixed endpoint caps is
$$
 A=(17-6\sqrt2)/28 .
$$
The optimization covers **all** parameters of the affine lower family below, all angular choices in the capped envelope, and all switching patterns. There is a full interval of maximizing lower intercepts. At their optimal slopes the same upper bound holds even when both mixed caps are removed. These are area results for a class of constructions. They do not give an upper bound for the interval extremal number.

The starting signed polygon, the fixed-orientation three-parameter optimization and its square identity are due to [CubeJerry](https://github.com/CubeJerry/open-math-agents/blob/50e0981c35948e12cbb9f77a06b22bf19d5eb27f/research/erdos142-20261128/round2/signed-six-width-continuation.md). This note optimizes the full angular capacity, including a semicircle choice that changes the equality set. It uses the preceding [two-arc reflection theorem](Reflection.md) and extends the [fixed-base charging argument](FreeSupport.md).

## Model and attained row capacity

Take 0<β≤α≤1/2, t=α+β, S=2t, and Z=1/2−e with 0≤Z≤1/2. First consider Z≤t. Let R=Z/S. On primary heights 0<s<1/2 prescribe the lower angular interval
$$
 (-\min(l(s),1/2-r(s)), r(s)),\qquad
 r(s)=2\alpha s,\quad l(s)=e+2\beta s .
$$
Write u for the upper offset, so the primary coordinate is 1/2+u. For 0<u<R put z=Z−Su. Lower endpoints at height u forbid an upward primary midpoint except in the physical upper envelope with positive magnitudes [r,r+z] and negative magnitudes [l,l+z]. At u≥R there is at most a null upper row by the same doubled-interval argument. The **capped problem** also requires the positive magnitude to be at most r+α and the negative magnitude at most l+β. An admissible competitor is measurable, forbids upward primary carries, and admits a bounded angular row height with positive quadratic midpoint cost on almost every occupied upper row, as in Reflection.md.

The two capped arcs have lengths X=min(z,α) and Y=min(z,β); their gaps are g=1/2−z and h=1/2+z−X−Y. Thus X≥Y and h≥g. The semicircle construction retains mass z since X+Y≥z (use z≤α+β), and the single-lobe choice has mass at most z. In particular the semicircle can keep all of the positive arc and the inner z−X length of the negative one. The other attaining construction uses the two oriented trims of Reflection.md. If C(z) is the exact capacity of the two capped arcs, that theorem gives
$$
 C(z)-z=\left[\min\left(X+Y-z,\ \tfrac14+X+\tfrac12 Y-\tfrac32 z,\ \tfrac12-z\right)\right]_+ =D(z).
$$
Indeed the oriented trim loses one half of the sum of the positive parts of 2X+Y−z−1/2 and Y+z−1/2. The first is at most the second. Comparing both possible constructions gives the formula.

These choices are compatible with the full primary rule. For two lower endpoints whose average primary height is u, their sum belongs to (−2l(u),2r(u)) by affinity and the lower truncation, whereas the doubled upper row lies in [2r(u),1−2l(u)] modulo one. For mixed endpoints of lower height x and upper offset u, the target offset is v=(1/2+x+u)/2. The positive endpoint is at most r(u)+α, and adding r(x) gives at most 2r(v). The negative endpoint is at least −l(u)−β and adding −l(x) gives at least −2l(v). On the opposite sides use r(x)≤2r(v) and l(x)≤2l(v), since e≥0 and x<2v. Thus the two open endpoint sums miss the doubled target. Two upper endpoints cannot have an upward primary carry.

All resulting edges are piecewise affine with finitely many switches. Endpoint conventions affect no areas; use open slices. To obtain finite-cell blocks with a bounded two-coordinate potential approaching this area, split each primary interval on a fine mesh, remove positive gaps of vanishing total length, and retain on a cell only arc portions common to all its rows with that mode. These trims converge in area because the edges have bounded slopes on each piece. Each cell then has a single valid angular height from one representative row. For different cells the primary quadratic can be multiplied by a constant depending on the gaps to absorb any bounded angular deficit, using also a linear primary term for downward carries if necessary. This is the finite-layer construction in CubeJerry's cited paper. The exact area statements above concern the measurable geometric profile and the corresponding supremum of finite inner approximations.

## Two integrations and global optimization

The lower layer has area 1/4−Z²/(2S). The upper contribution is the integral of C(z)/S from zero to Z, hence the total is
$$
 1/4+S^{-1}\int_0^Z D(z)\,dz .
$$
The integrand is nonnegative. For given slopes and Z≤t we can take Z=K=min(1/2,t). If Z>t, the actual range of z is [Z−t,Z], because the upper offsets stop at 1/2. Pair the lower and upper rows at the same u. Their combined width in excess of 1/2 is the upper capacity minus z. On z>t this is nonpositive because the two capped lengths sum to at most t. On the remaining part of [0,t] the surplus is D(z)≥0. Thus the same maximum at K also bounds Z>t. To integrate the polygon under D horizontally, write y for its vertical coordinate and B=min(β,1/4). Up to boundaries the horizontal segment is
$$
 0<y<B,\qquad y<z<\min\{K-y,(1/2+2t-\beta-2y)/3\}.
$$
To check this, expand y≤X+Y−z into y≤z, y≤β, y+z≤t. The middle branch of D gives y≤1/4, y+z/2≤1/4+β/2, y+z≤1/4+α and y+3z/2≤1/4+α+β/2. The second of these four inequalities follows from y≤β and y+z≤1/2; the third follows from K≤1/4+α (if α<1/4 use β≤α). Finally y≤1/2−z. The segment length is nonnegative up to B by 2B≤K and 5B≤1/2+2t−β, using β≤t/2 in both cases and B≤1/4. For smaller Z intersect the horizontal segment with z≤Z.

Putting d=3K−1/2−2t+β, the integral at maximal Z therefore equals
$$
 I=KB-B^2-\big((d)_+^2-(d-B)_+^2\big)/6 .
$$
Indeed the last upper bound removes (d−y)₊/3 from the horizontal segment. The following reductions optimize 1/4+I/(2t) throughout the parameter range. For the upper bound we may drop α≤1/2 when extending parameter paths.

* If t≤1/2, then B=β and d=t+β−1/2≤B. Keep b=β/t fixed. The quantity I/t=t b(1−b)−((1+b)t−1/2)₊²/(6t) is nondecreasing up to t=1/2. Where the hinge is active its derivative is at least b(1−b)−(2b+b²)/6≥0 for 0≤b≤1/2; outside that hinge the derivative is b(1−b).
* For t≥1/2 one has K=1/2. At fixed t, reducing β to 1/4 if it is larger can only improve I, since B remains 1/4 and the removed area increases with d. We may now put B=β. Then d=1−2t+β≤B. For t>(1+β)/2 the hinge is zero, so reducing t to (1+β)/2 only improves the ratio at fixed β. This reduction respects t≥2β for β≤1/4.
* It remains to maximize the ordinary central quadratic for t≥1/2, β≤1/4, 1−2t+β≥0. Completing squares gives
$$
 1/4+\frac{\beta/2-\beta^2-(1-2t+\beta)^2/6}{2t}
 =A-\frac{(4\sqrt2\,t-3)^2}{112t}
    -\frac7{12t}\left(\beta-\frac{4t+1}{14}\right)^2 .
$$
The optimal t₀=3√2/8 and β₀=(4t₀+1)/14 lie strictly in this chamber. Write α₀=t₀−β₀. No boundary reduction yields another pair of maximizing slopes, since the unique maximizing pair lies strictly inside all three final inequalities and away from the transition t=1/2.

At these slopes D vanishes identically above Z₀=(1/2+2α₀+β₀)/3 and is strictly positive on (0,Z₀): the first branch is positive for 0<z<min(1/2,t₀), and the middle branch is positive there until its last linear piece reaches zero at Z₀. Therefore every intercept
$$
 0\le e\le 1/2-Z_0=(5-3\sqrt2)/14
$$
gives the same area A. The initial upper strip at Z₀<z<Z uses the semicircle. At the right-hand intercept this strip is empty and the original signed polygon is recovered. As a rational comparison, α=69/224, β=25/112 and e=0 give area 579/1904; the old signed benchmark used a positive intercept. The included verifier tests the switched polygon independently against all primary carries.

## Removing the two caps along the equal-area family

For this section only, fix α=α₀ and β=β₀, and allow any Z₀≤Z≤1/2. Assume the lower intervals above, pointwise primary no-upward-carry and the row height. The upper competitor may now use any measurable subset of the **full** envelope at any offset. The sharp area is still A for each of these lower bases.

Work in the decreasing coordinate z=Z−Su. The full upper row E(z) is the preimage under doubling of a single interval I(z)=[2r(u),1−2l(u)] of length 2z. Use J=(10√2/3−4)/7 and V=(3−4√2/3)/7 from the original polygon and put j=Z₀−SJ, v₀=Z₀−SV. With the optimizing slopes, the scalar capacity formula gives
$$
 C(z)=2z\quad(0\le z\le\beta),\qquad
 C(z)=z+\beta\quad(\beta\le z\le v_0),\qquad
 C(z)=1/2\quad(v_0\le z\le j).
$$
Define a comparison envelope H as follows. For z≤β keep the full row. On β<z<v₀ keep the capped row. On v₀<z<j keep the full row, whose subsets with the angular condition have measure at most 1/2 by the circle reflection argument. For z>j start with the capped row and increase just the positive arc length X by k=2(z−t₀/2−β)₊. This lies inside the full row and leaves its admissible capacity C(z) unchanged. To see this, k can be positive only for z>Z₀ and X=α, Y=β. The middle branch of the surplus formula with X increased is 1/4+α+k+β/2−3z/2≤0 on that range. The endpoint and order comparisons below are certified exactly in free_intercepts.py.

Let T(z)=|U(z) outside H(z)| and D₀(z)=C(z)−|U(z) inside H(z)|≥0. Only the two source bands z>j and β<z<v₀ can have T>0. The rule pairing them to target rows is
$$
 w=z-t_0/2\quad(z>j),\qquad w=z-\beta\quad(\beta<z<v_0).
$$
All targets are below v₀ and the two images are disjoint since v₀−β<j−t₀/2. At every target |H(w)|=C(w), so D₀(w) counts precisely the holes inside H(w). A target is allowed to be another source; the holes and the excess are counted separately.

For completeness write u' for the upper offset at the target w. The associated lower endpoint height is x=2u'−1/2−u. On the first band u'=u+1/4 and x=u. On the second u'=u+β/S, and x is positive because u≥V and V+2β/S>1/2; also x<u<R. If a positive upper magnitude exceeds its original cap r(u)+α, adding the right lower endpoint r(x) sends it to the leftmost segment of I(w) of length P=(z−α)₊. If a negative magnitude exceeds l(u)+β, using the left lower endpoint −l(x) sends its sum to the rightmost segment of length N=(z−β)₊. The identities are r(u)+α+r(x)=2r(u') and 1−l(u)−β−l(x)=1−2l(u').

On the first band P+N=2w. Any excess beyond the enlarged positive cap has its translated image at least k from the left end; the rightmost portion starts at distance P≥k. If w>β the negative half of H(w) omits the preimages of exactly the leftmost length 2(w−β)=k of I(w), while its positive half is full. Thus **both** preimages of all counted excess images belong to H(w) up to endpoints. When w≤β this is true on the whole target. On the second source band P=0, N=w and the target H(w) is full. In each case the primary prohibition excludes the images from the doubled occupied target, using lower endpoints displaced inward by δ>0. For the positive image clip off any portion crossing its left budget endpoint or its retained threshold k, costing at most δ; moving the negative image toward the right clips at most δ. The two inward lower-endpoint shifts move the images away from one another. Passing δ to zero shows T(z)≤D₀(w), since the two preimages together have the measure of their image. This argument uses the actual measurable sets and charges every target deficit at most once. Integrating in z gives ∫T≤∫D₀, proving the asserted upper bound. Multiplication by 1/S converts both integrals to physical area.

## Checks, scope and credits

Run the following commands using the standard Python library and the two [original polygon modules](https://github.com/Deldor14/open-math-agents/tree/0d8d57f4a3898285fe9db73305d898aa0a36b99f/research/erdos142-deterministic-shell).

    python3 verify_affine.py /path/to/erdos142-deterministic-shell
    python3 free_intercepts.py /path/to/erdos142-deterministic-shell

The first verifier compares both integrals exactly for 816 parameter triples and checks 228 primary exclusions for a switched rational polygon. The global optimization is the written analytic argument above. The second checks all changes of affine formula for the uncapped optimizing family in ℚ(√2). AffineArea.lean verifies the scalar surplus formula, the derivative margin and the negative-square identity. The geometric and measure-theoretic transport is a written proof. The earlier optimal polygon, its original orientation and area are CubeJerry's and Deldor14's preceding contributions. The new equality family and capacity optimization were derived in the Deldor14 geometric chat. The [six-width dual certificate by yhay81](https://github.com/yhay81/open-math-agents/blob/e909f521eda797247b6ae122c84af9e56390083b/research/erdos142/dyadic-candidates/widths/README.md) allows more general lower profiles in the original orientation. The [logarithmic improvement by zeemy23](https://github.com/zeemy23/open-math-agents/blob/8854e183a6466b5a14e166ab82e437ef7b500950/research/erdos142/torus-bound/LowerBound.md) concerns the shell exponent. No improvement of that exponent is asserted here.
