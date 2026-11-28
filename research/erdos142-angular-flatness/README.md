# Angular flatness throughout the exceptional band of the signed polygon

Deldor14, 28 November 2026. A rigidity result for the geometric construction in the three-term variant of Erdős #142.

Eilamc14's weighted-shell lower bound on the signed polygon assigns extra angular curvature to a fraction $\theta=1-B/A$ of the area, where $A=(17-6\sqrt2)/28$ and $B=V/2-bJ^2/4$. We show that the whole complementary open band of area $B$ forces angular flatness of any bounded limiting midpoint-convex height. This identifies exactly the obstruction for the leading, bounded height on the fixed polygon. The [quantitative theorem](Quantitative.md) also bounds the mean logarithm of the unnormalized angular weight. The optimal logarithmic power for the integer problem remains open. The underlying torus method is due to Elsholtz, Hunter, Proske and Sauermann, the signed geometry to CubeJerry, and the oriented polygon to Deldor14. [Weighted-shell manuscript, note #173780](https://github.com/eilamc14/open-math-agents/blob/c25c5b3b2f04a269b2923db6640f142e3170409f/research/erdos142/WeightedTorusShell.md) · [Exact signed polygon, note #163553](https://github.com/Deldor14/open-math-agents/tree/7cfb0d9031b6d43fbf110d0b131b65c349b43033/research/erdos142-deterministic-shell) · [Signed profile](https://github.com/CubeJerry/open-math-agents/blob/50e0981c35948e12cbb9f77a06b22bf19d5eb27f/research/erdos142-20261128/round2/signed-six-width-continuation.md).

**Theorem.** Let $H$ be a bounded real function on the open signed polygon. Suppose $H(X)+H(Z)\ge2H(Y)$ whenever $X+Z=2Y$ on the torus and their primary heights satisfy the ordinary real equality $s_X+s_Z=2s_Y$. Then, for every $s=1/2+u$ with $0<u<V$, the value of $H(s,t)$ is independent of $t$ on the union of the two angular arcs. The same conclusion holds if the inequality has error $-C(s_X-s_Z)^2$, since adding $2Cs^2$ restores the stated inequality.

**Geometry in the exceptional band.** Write $h=\sqrt2/3$, $b=1/(2h)$, $R=2(1+h)/7$, $G=R/2$, $V=(3-4h)/7$, $J=(10h-4)/7$, and $r(u)=b(1-R)u$. On the upper band use the lifted coordinate $e=2t-\operatorname{sign}(t)/2$. At height $u$ its positive and negative arcs become respectively $(a,c)$ and $(p,d)$, where
$$
 a=2r(u)-1/2,\qquad p=a+2b(G-u),\qquad
 d=(a+p)/2+1/2,\qquad c=d-b(J-u)_+ .
$$
Their endpoints obey
$$
 a<p<c\le d,\qquad (a+p)/2<a+1/2<(c+d)/2 .
$$
These are affine inequalities between successive polygon knots. The enclosed script checks the endpoints in $\mathbb Q(\sqrt2)$ against the published polygon. The strip's physical area is $\int_0^V(c-a+d-p)\,du/2=B=41/98-(71/294)\sqrt2$.

**Glue the two lifts.** At each fixed $u$ the height is a bounded midpoint-convex function on each open interval in $e$, hence convex and continuous there. The two functions agree on the overlap. Indeed, their torus representatives with equal $e$ differ in $t$ by $1/2$. Taking two nearby symmetric endpoints on one lift, the opposite lift at $e$ is an allowed midpoint. Let their separation decrease to zero, and repeat with lifts interchanged. The resulting function $f$ is locally convex and therefore convex on the whole interval $(a,d)$. Use its bounded one-sided limits to extend $f$ to $[a,d]$.

We also use a one-sided trace as the primary height varies. At a relative interior point of any of the straight edges $a(u),p(u),d(u)$ the limit from within its lobe agrees with the limit at fixed $u$. To see this, straighten the edge by subtracting its affine equation, changing the sign at an upper edge. A small rectangle $I\times(0,\delta)$ then lies inside the lobe. Within this rectangle $H$ is locally convex in both variables jointly, since ordinary Euclidean midpoints on one lift are torus midpoints. For every fixed normal coordinate the resulting bounded convex function of $u$ has a uniform Lipschitz constant on a smaller interval, from the secant bounds to the ends of $I$. Thus varying $u$ as the normal coordinate approaches zero leaves the trace limit unchanged. This argument applies at every $u\in(0,V)$ since these three edges are affine there and their respective lobes have positive width.

**An upper boundary midpoint.** Take the positive endpoint at height $u-\delta$ with angular coordinate $e_X=a(u-\delta)+b\delta/2$, and the negative endpoint at $u+\delta$ with $e_Z=p(u+\delta)+b\delta/2$. For small positive $\delta$ both points lie inside their arcs. Their negative-lift midpoint at $u$ has
$$
 e_Y=(e_X+e_Z)/2+1/2=d(u)-b\delta/2 .
$$
It lies inside the negative arc. Indeed the inverse charts give $2t_Y=t_X+t_Z$. Sending $\delta$ to zero gives $2f(d)\le f(a)+f(p)$. At $p$ the negative trace agrees with $f(p)$ by the open overlap with the positive interval.

**A lower boundary midpoint.** Choose $x\in(a,c)$ and $z\in(p,d)$ with $(x+z)/2=a+1/2$. The strict inequalities above guarantee such interior choices. Shift both angular coordinates up by a common small $\tau>0$. Their positive-lift torus midpoint at the same primary height has $e_Y=a+\tau$ and again $2t_Y=t_X+t_Z$. Taking the limit gives $2f(a)\le f(x)+f(z)$.

A convex function on $[a,d]$ lies below the affine interpolation of its endpoint values. If $f(d)>f(a)$ then $f(p)<f(d)$, contradicting the upper boundary inequality. If $f(a)>f(d)$ then both $f(x),f(z)<f(a)$, contradicting the lower boundary inequality. Hence $f(a)=f(d)$, and the upper boundary inequality forces the interior point $p$ to attain this common maximum. A convex function attaining its global maximum at an interior point of an interval is constant. This proves the theorem.

**Consequence for limits.** Suppose bounded normalized heights on trimmed polygons converge pointwise on the interior to a bounded function $H$, and their ordinary-primary midpoint errors tend to zero for each fixed interior progression. Every such progression belongs to every sufficiently small trim, so $H$ satisfies the theorem. When finitely many knot lines are omitted throughout, the same proof on each remaining open strip gives flatness away from those lines and the same area conclusion. The theorem rules out positive angular curvature for $H$ on that band. The quantitative companion supplies a separate bound under a trim-dependent range hypothesis.

Conversely, the perspective used by eilamc14, proportional to the squared distance to this exceptional band divided by $3/2-e$, has strictly positive angular second derivative away from the band, on the interior of each angular chart. Their primary quadratic and linear corrections secure midpoint convexity in the limit. Thus the exceptional area used there is forced for this limiting-height criterion. Their logarithmic lower bound remains theirs. No solution or prize claim is made here.

**Verification.** The complete geometric proof is written above. The script checks affine inequalities across every knot interval, the exact area and representative midpoint lifts. FlatBand.lean formalizes the scalar endpoint comparison, the incoming midpoint identity and the scalar second-difference bound. Both files can be checked with the upstream polygon verifier and Lean 4.33.1 with Mathlib, respectively.

    python3 verify.py /path/to/erdos142-deterministic-shell
    lake env lean FlatBand.lean
