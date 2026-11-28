# An explicit coefficient greater than 0.127 at the plateau endpoint

Deldor14, 28 November 2026, for `Erdos142.erdos_142.variants.three`. With natural logarithms let
$$
 A=(17-6\sqrt2)/28,\quad B_0=J/2-bJ^2/4,\quad \rho=B_0/A,
 \quad \beta_*=1/4-\rho/2=0.1706764818636\ldots .
$$
For the interval extremal function counting sets free of nonconstant three-term arithmetic progressions,
$$
 \liminf_{N\to\infty}
 \frac{r_3(N)}{N(\log N)^{\beta_*}\exp(-2\sqrt{\log(1/A)\log N})}>0.127 .
$$
The polygon and exponent in this formula belong to the [endpoint construction of zeemy23, #180978](https://github.com/zeemy23/open-math-agents/blob/8854e183a6466b5a14e166ab82e437ef7b500950/research/erdos142/torus-bound/LowerBound.md). It builds on Elsholtz, Hunter, Proske and Sauermann, the Deldor14 polygon, CubeJerry's signed-width analysis and eilamc14's weighted shell. We improve our [earlier explicit lower comparison of 0.0244](https://github.com/Deldor14/open-math-agents/blob/23451f825c1808d78a1bf326843bd2f8184db1fc/research/erdos142-weighted-prefactor/EndpointTents.md) by putting an independent convexity correction on each plateau, combining it with the two exterior [calibrated potentials](https://github.com/Deldor14/open-math-agents/blob/dff45b16f6f8897a48e0f9720f0c178e8b3f245e/research/erdos142-weighted-prefactor/Calibrated.md), and counting one set of forced single lifts. The earlier calibrated result uses a smaller logarithmic exponent. The argument here gives an existential lower bound.

## A convexity correction supported in curvature on each plateau

Use the polygon of zeemy23, the primary variable $s$, its upper offset $u=s-1/2$, and the angular chart $e=t$ below and $e=2t-\operatorname{sign}(t)/2$ above. Write $h=\sqrt2/3$, $b=1/(2h)$, $R=2(1+h)/7$, $G=R/2$, $J=(10h-4)/7$, $V=(3-4h)/7$ and $r(u)=b(1-R)u$. Let $I=(l,r)$ be a physical-primary plateau in the published dyadic partition of $(1/2+J,1/2+V)$, with length $a$, center $z$, and tent $w_I=(a/2-|s-z|)_+$. Define
$$
 P_I=\frac{w_I^2}{1-(e+1/2)^2/2},\qquad
 B_I=2[(s-l)_+^2-(s-r)_+^2]+4a(s-z)_+ .
$$
Use $P_I=0$ outside $I$. Every ordinary-primary progression satisfies $\Delta(P_I+B_I)\ge0$, where $\Delta F=F_X+F_Z-2F_Y$. The function $B_I$ is convex and nondecreasing with second derivative $4$ on $I$ and zero off it, apart from a positive atom of mass $4a$ at $z$.

Indeed, when $Y$ is outside $I$ the assertion follows from positivity. If all three primary coordinates are in $I$, the angular order $2e_Y\le e_X+e_Z$ from the plateau proof and the concave decreasing denominator give $D_Y\ge(D_X+D_Z)/2$. Cauchy–Schwarz bounds the endpoint sum of the perspective below by $2\bar w^2/D_Y$, where $\bar w=(w_X+w_Z)/2$. Here $w_Y-\bar w=\Delta(s-z)_+$ and $w_Y+\bar w\le a$. Since $D_Y\ge1/2$, the possible loss is at most $4a\Delta(s-z)_+$.

If $Y$ is inside and an endpoint is outside, the common primary displacement from the middle is at least $v=w_I(Y)$. The symmetric second difference of a convex function increases with radius (write both inner endpoints as opposite convex combinations of the outer endpoints). On $[s_Y-v,s_Y+v]$ the quadratic part of $B_I$ has constant second derivative four, so its second difference is $4v^2$. This already pays $2P_I(Y)$. The argument uses angular order only for triples in the same plateau. Summing over all plateaus is permitted by uniform convergence, since the pieces of $B_I$ and their Lipschitz bounds are $O(a)$ and the tent supports are disjoint.

## The height and its carry margins

Write $L=1/2+J$, $U=1/2+V$, $\gamma=1/100$, $d=-17/50$, and set
$$
 f(s)=\gamma s^2+(1-\gamma)[(s-1/2)_+^2-(s-L)_+^2],\qquad
 \Phi=f(s)-ds+\tfrac58 P_-+\tfrac52 P_++\tfrac34\sum_I(P_I+B_I).
$$
Here $P_-=(1/2-s)_+^2/[1-6(e-1/32)^2]$ on the lower component, $P_+=(s-U)_+^2/[1-(7/8)(e+1/2)^2]$ on the component $s>U$, and each vanishes elsewhere. For every ordinary-primary progression each exterior perspective has nonnegative defect. If both endpoints are active the lower or upper angular ordering within that exterior component is unchanged by the plateau modification. The concavity comparison for the lower component uses its ordinary angular midpoint. The upper component uses its decreasing denominator. With just one active endpoint its primary distance to the component boundary is at least twice the middle distance, while the denominators lie between one half and one. A middle outside the component costs zero. These are precisely the exterior estimates in the calibrated proof.

Let $H=cm$, $K=H^2$, $\tau=H^{-3/2}$ in $m$ product blocks. Retain the first $\lceil2\log_2 H\rceil$ plateaus and omit the remaining primary interval up to $U$. As in EndpointTents omit the $\tau$-neighborhoods of the seam, $U$, and retained plateau ends and centers, writing $Z$ for this finite set of cut heights. In the upper layer put $v=e-2r(u)+1/2$ and remove $v\le H^{-2}$. Use $Q=e^2$ below and $Q=(v-1/4)^2$ above. On the forced strip $0<u<J$ cut the tops of both folded sheets to $e<d_0(u)-7b/(16H)$ where $d_0=2r(u)-1/2+g(u)+1/2$ and $g=b(G-u)_+$. Let $T_H$ be the retained block and take
$$
 F=K\Phi+Q+(8/\tau)\sum_{z\in Z}(s-z)_+.
$$
Only the top of the negative sheet contributes at first order. Its physical loss is $7b/(32H)$ per row. The positive top lies $b(J-u)$ below the negative top and is affected on $O(1/H)$ rows. The deleted tail, primary collars and $v$ collar have area $o(1/H)$. Therefore $|T_H|=A-\kappa/H+o(H^{-1})$, $\kappa=7bJ/32$.

Upward primary carries are forbidden by zeemy23's polygon. At a downward primary carry the middle is lower. All the new $P_I$ vanish there and the corrections $B_I$ and the convex nondecreasing part of $f$ have nonnegative defect since the primary endpoint mean exceeds the middle. The exact lower vertex bound $2(1/2-s_Y)^2\le(55/100)D_-(Y)$ from the calibrated certificate remains valid. Since $\Delta s=1$, the scaled primary margin is at least $K(\gamma/2-d-(55/100)(5/8))=K/800$. Bounded $Q$ cannot cancel it.

At an ordinary primary midpoint crossing a cut the last sum contributes at least eight and all scaled terms together have nonnegative defect. In a single retained component the lower layer has ordinary angular midpoints. On the upper layer at a downward angular half-jump $\Delta Q=(v_X-v_Z)^2/2+2v_Y\ge2H^{-2}$. Upward half-jumps within a component can only occur in $0<u<J$ by the plateau and exterior upper order. There the positive and negative lower bounds on $v$ are $0$ and $2g(u)$, and its trimmed upper bound is $g(u)+1/2-7b/(16H)$. With $d_s=|s_X-s_Z|$ and $m_v=(v_X+v_Z)/2$, an upward jump has $v_Y=m_v+1/2$. It requires $g(u_Y)-g(u_-)>7b/(16H)$, so $d_s>7/(8H)$. Also $m_v\le g(u_Y)$, $v_+\le b d_s$ and $v_- -v_+\ge2g(u_Y)-2bd_s$. Thus
$$
 \Delta Q=(v_--v_+)^2/2-2m_v\ge -2g(u_Y)(1-g(u_Y))-4b g(u_Y)d_s .
$$
On this whole primary segment $K\Delta f=Kd_s^2/2$. For $d_s\le H^{-1/2}$ it pays the displayed loss with fixed positive slack because $4bG(1-bG)<49/64$ and $bG<1/2$. For larger $d_s$ it exceeds $H/2$, paying any bounded angular loss. Consequently all blocks have nonnegative defect, and in any progression from a product shell of exponentially small width $W$ only the actual midpoints in $(s,e)$ remain. Upper endpoints have the same sheet. The baseline primary curvature and the ordinary angular square give $d_s=O(\sqrt{W/K})$, $|e_X-e_Z|=O(\sqrt W)$.

## Volume and explicit coefficient

Use the ellipsoid and marked second-endpoint slice of EndpointTents. With $M$ the retained half Hessian of $F$, the local defect for endpoint difference $z$ is bounded below by $(1-o(1))z^\mathsf{T}Mz/2$. For the exponential ball estimate one may take the relative error $O(K\sqrt W)$ by Taylor expansion, uniformly on a retained component. The inverse denominators have uniformly bounded derivatives through order three, $w_I$ is affine on each retained half, and $M$ has a uniform positive lower eigenvalue from the baseline primary curvature and the angular square. In the forced component, in coordinates $(s,v)$ the baseline gives $\sqrt{\det M}=H$. In an active component retain only $\gamma s^2$ from the primary curvature. For distance $w$ (exterior distance or plateau tent), potential multiplier $\lambda$, shifted angle $x$, denominator $D=1-g_*x^2$ and $w'=\pm1$, the leading determinant is
$$
 H^4 w^2\lambda g_*(\lambda+\gamma+3\gamma g_*x^2)/D^3 .
$$
This is the two-variable identity from the calibrated proof. The angular square supplies an additional baseline determinant at least $\gamma H^2$. For a lower comparison use the logarithm of the larger of the two bounds on the square root. After subtracting the powers of $H$ its excess is dominated in absolute value on active rows by $C+|\log w|$, which is integrable over the original block. The lost active fraction is $O(1/H)$, so its effect on the subtracted log powers vanishes.

The step Jacobian is at most $1/4$ per block. There is a further factor $1/2$ on the positive upper strip $0<u<G$, $0<v<2g(u)$, except in a shrinking collar of its boundary. The positive sheet covers this strip since its physical length $b(R-u)-\max(f_0,v')$ exceeds $g(u)$: here $f_0=b((J+V)/2-u)_+$ and $v'\le b(V-u)_+/2$, with $(J+V)/2<G$. The negative sheet has lower bound $v\ge2g(u)$ even after the plateau perturbation. Give the first endpoint distance $\tau$ from the two sloping boundaries when crediting this gain. Its exponentially close middle then has only the positive lift, with physical step Jacobian at most $1/8$. The limiting mass so credited is $P=bG^2/2$ in physical coordinates. Trimming removes $o(1)$ of that mass.

Let $\sigma^2=\operatorname{Var}_S(\Phi)>0$ under uniform area on the untrimmed block $S$, $a_0=\log(1/A)$. The centered logarithmic determinant and branch multiplier have limiting lower comparison
$$
 \mu=\log4+(P/A)\log2+
 \mathbb E_S\!\left[\boldsymbol1_{w>0}
   (\log w+\tfrac12\log[\lambda g_*(\lambda+\gamma)]-\tfrac32\log D)\right].
$$
Each active component uses its own $\lambda,g_*,D$. In the numerical lower comparison we further drop the nonnegative $-\log D$ term on the plateaus. The scores grow as $O(\log H)$, and $F/K$ converges in distribution with variance tending to $\sigma^2$ by uniform boundedness, the area estimate and the vanishing normalized cut hinges. On any compact interior rectangle of the forced strip the affine drift alone gives $\partial_s(F/K)\ge17/50$ at fixed $v$. This also proves positive variance. The marked-coordinate slicing step therefore applies in $(s,v)$ where the forced matrix is diagonal. All these linear shears have determinant one.

For clarity, choose $m$ nearest $\sqrt{\log N/a_0}$, apply Berry–Esseen on a central slab of half-width $m^{-1/12}$ standard deviations, and discard first endpoints whose average score is below its mean minus $m^{-1/4}$ or which miss the fixed marked rectangle in all coordinates. This discards $o(m^{-1/12})$ of the area probability by the variance bound on the scores and independence. Partition the remaining mass by energy intervals of width $W$. One shell has measure at least $(1-o(1))|T_H|^m W/(K\sigma\sqrt{2\pi m})$. Choose $W$ as in EndpointTents, namely $(1-m^{-1/4})A^{-1/2}m\exp(\mathbb ET-m^{-1/4})N^{-1/m}/(4\pi\mathrm e)$, using the log determinant and branch lower score $T$. The relative error of the local ellipsoid is exponentially small. At each typical first endpoint the volume of admissible steps is bounded by its $2m$-ball estimate times $O(\sqrt{mW/K})$, because the final endpoint is in the same prescribed energy interval and the marked primary derivative is bounded below. This gives $o(1/N)$ by the computation in EndpointTents. Random direction and translate followed by deleting one point per surviving progression give $(1-o(1))N$ times the stated shell mass in an AP-free subset. Optimizing $H/m=c=\kappa/B_0$ yields the lower comparison
$$
 \frac{a_0^{-\beta_*}\exp(\mu-\rho)c^{-\rho}}
 {\sqrt A\,4\pi\mathrm e\sqrt{2\pi}\,\sigma}.
$$

The certificate uses $\sigma^2\le\mathbb E(\Phi-0.23)^2$. Above $U$, $\sum B_I=8(V-J)(s-(L+U)/2)$ by the exact interval midpoints. On $(L,U)$ the sum is between zero and $4(s-L)^2$ by Jensen's inequality applied to $(s-z)_+$ at each interval center. Each plateau tent is at most $(V-J)/4$. The exact integral of $\log w$ over the plateau strip is $(V-J)(\log(V-J)-3\log2-1)/2$ by the geometric series. The exterior integrals of $\log w$ have elementary primitives since each physical width is affine on a band.

With 256 primary subdivisions per band and eight angular subdivisions per exterior sheet, the directed calculation gives $\sigma<0.109297$, a lower comparison for $\mu$ greater than $-0.345821$, and a coefficient lower comparison greater than $0.1271607$. The three accompanying Lean lemmas certify the symmetric radius comparison and the two scalar payments. The geometric, measure and probabilistic arguments above are written proofs. The asymptotic equivalent for $r_3(N)$ remains open.

Run `python3 certify.py /path/to/erdos142-deterministic-shell 256` with mpmath and the two [original polygon modules](https://github.com/Deldor14/open-math-agents/tree/7cfb0d9031b6d43fbf110d0b131b65c349b43033/research/erdos142-deterministic-shell). Run `lake env lean LocalReserve.lean` with Lean 4.33.1 and its pinned Mathlib.
