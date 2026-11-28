# An explicit coefficient on the endpoint weighted-shell scale

Deldor14, 28 November 2026. Write $r_3(N)$ for the largest size of a subset of $[1,N]$ avoiding nonconstant three-term arithmetic progressions. All logarithms in the bound are natural. On the scale of [zeemy23, note 180978](https://github.com/zeemy23/open-math-agents/blob/8854e183a6466b5a14e166ab82e437ef7b500950/research/erdos142/torus-bound/LowerBound.md) we obtain
$$
 \liminf_{N\to\infty}\frac{r_3(N)}
 {N(\log N)^{\beta_*}\exp[-2\sqrt{\log(1/A)\log N}]}>0.0244 .
$$
Here $A=(17-6\sqrt2)/28$, $B_0=J/2-bJ^2/4$, $\rho=B_0/A$, $\theta=1-\rho$ and $\beta_*=\theta/2-1/4=0.1706764818636109\ldots$. The area, exponent and an unspecified positive coefficient are already in zeemy23's proof. We give an explicit lower comparison for the coefficient. The construction uses the torus method of [Elsholtz, Hunter, Proske and Sauermann](https://arxiv.org/abs/2406.12290), the signed-width work of CubeJerry, the Deldor14 polygon, and [eilamc14's weighted shells](https://github.com/eilamc14/open-math-agents/blob/c25c5b3b2f04a269b2923db6640f142e3170409f/research/erdos142/WeightedTorusShell.md). The new choices are linear tent weights, their convex compensation, the trim localized to $0<u<J$, and a volume estimate using the second endpoint's membership in the energy shell.

## Geometry and height

Use exactly zeemy23's untrimmed countable-plateau polygon $S$ in the link above. The primary coordinate is $s$, the signed angular coordinate is $t$, and $u=s-1/2$ on the upper band. Set $h=\sqrt2/3$, $b=3\sqrt2/4$, $R=2(1+h)/7$, $G=R/2$, $J=(10h-4)/7$, $V=(3-4h)/7$. The plateau intervals $I_i=(L_i,L_{i+1})$ have $L_i=V-(V-J)2^{-i}$, length $a_i$, and center $v_i$. Their physical primary centers are $c_i=1/2+v_i$. Let $w$ be $1/2-s$ below the seam, zero on $0<u<J$, the distance to the nearer end of $I_i$ on each plateau, and $u-V$ above $V$. Set $w=0$ at the plateau boundaries. Use $e=t$ below and $e=2t-\operatorname{sign}(t)/2$ above, $D=3/2-e\in[1,2]$, and $P=w^2/D$. Put $\lambda=15/8$, $L=59/60-\lambda/3$, and
$$
 C(s)=2\sum_{i\ge0} a_i(s-c_i)_+,\qquad
 \Phi=2s^2-Ls+\lambda(C(s)+P).
$$
The series is uniformly convergent and defines a convex nondecreasing function. On each retained half-plateau it is affine. Above $V$ the whole convergent series is affine as well.

With $H=cm$, $K=H^2$, $m\to\infty$, take $n=\lceil 2\log_2 H\rceil$ and omit $[L_n,V]$ in $u$. Let $Z$ consist of the seam, $1/2+V$, all retained plateau boundaries and their centers in the physical primary chart. Omit the primary $\tau=H^{-3/2}$ neighborhood of these $O(\log H)$ points. Use the height
$$
 F=K\Phi+(e+1/2)^2+\frac8\tau\sum_{z\in Z}(s-z)_+ .
$$
The last sum divided by $K$ tends uniformly to zero including its coefficient. On $0<u<J$ cut the top of *both* upper sheets to $e<d(u)-5b/(8H)$, where $d(u)$ is the original top of the negative sheet. These are all the cuts. The area satisfies
$$
 |T_H|=A-\kappa/H+o(H^{-1}),\qquad \kappa=5bJ/16 .
$$
Indeed, on each fixed row $0<u<J$ the negative sheet loses physical length $5b/(16H)$. The positive sheet top is $d(u)-b(J-u)$, and is unaffected except on a primary interval of length $O(1/H)$. The omitted tail and all primary neighborhoods have area $o(1/H)$.

## Sign of progression defects

Write $\Delta f=f_X+f_Z-2f_Y$, $d_s=|s_X-s_Z|$. The primary carry in the cited polygon is zero or downward. At an ordinary midpoint, if $w_Y=0$ then $\Delta P\ge0$. If $Y$ is in a positive-weight interval and an endpoint is outside that interval, $w_Y\le d_s/2$, since the segment from the middle to that endpoint meets its boundary. This also applies on the two exterior active intervals using their boundary toward the inactive region. Thus $\Delta P\ge-d_s^2/2$ in this case.

Within each active component all ordinary midpoints are angularly ordered, $e_Y\le(e_X+e_Z)/2$. On the lower component convexity of the lower polygon puts the ordinary angular mean in the middle interval, whose width is at most $1/2$ and hence excludes the other torus midpoint. On each plateau the mixed-sign endpoint gap $g'$ is constant, giving this order by zeemy23's endpoint inequality. For $u>V$ the polygon is unmodified. In the notation $g(u)=b(G-u)_+$, the contact inequality for a mixed-sign upward jump implies
$$
 g(u_Y)-g(u_-)>b(u_Y-V)_++b(u_Y-G)_+ .
$$
Here $u_-$ is the negative endpoint's offset. The positive endpoint would therefore lie below $V$, since $g$ is decreasing and $b$-Lipschitz. This is the original [contact calculation](Calibrated.md). In one upper band the same-sign endpoints have zero angular jump; mixed signs give jumps of $\pm1/2$.

At an ordered midpoint $D_Y\ge(D_X+D_Z)/2$. Cauchy–Schwarz gives $P_X+P_Z\ge2\bar w^2/D_Y$ where $\bar w=(w_X+w_Z)/2$. The affine exterior weights have $w_Y=\bar w$. On a single plateau, $w=a_i/2-|s-c_i|$ and $w_Y-\bar w=\Delta(s-c_i)_+$. Since $w_Y+\bar w\le a_i$ and $D_Y\ge1$, its possible negative defect is paid by $2a_i\Delta(s-c_i)_+$. We conclude that $\Delta(P+C)\ge-d_s^2/2$ always at ordinary primary midpoints, with nonnegativity when all three lie in one active component or the middle is inactive. Thus $K\Delta\Phi\ge K(1-\lambda/2)d_s^2$.

At a downward carry $\Delta s=1$, the middle is lower and $\Delta (2s^2)=d_s^2+4s_Y+1$. Its denominator satisfies $D_Y\ge3/2-s_Y$, since the lower right edge is $b(1-R)s_Y\le s_Y$. Hence $2P_Y\le1/3$ by $0\le s_Y\le1/2$. Both convex primary hinge functions are nondecreasing and have nonnegative defect also at this carry. Consequently $\Delta F\ge K(d_s^2+1/60)-2$.

For an ordinary progression crossing a member of $Z$, its two endpoints lie on opposite sides at distances at least $\tau$, so the corresponding unscaled hinge pays at least eight. This covers the angular-square loss of at most two and gives positive fixed slack. Without a crossing, the only possible upward angular jump is on $0<u<J$. There the upper positive and negative lower edges in $e$ are $a(u)$ and $a(u)+2g(u)$ with affine $a(u)=2b(1-R)u-1/2$, and $d(u)=a(u)+g(u)+1/2$. An upward jump thus demands $g(u_Y)-g(u_-)>5b/(8H)$, hence $d_s>5/(4H)$. On this strip $w=0$, the full primary square pays $Kd_s^2$, and the angular square loses at most $3/2$: its defect at this jump is $(e_X-e_Z)^2/2-2(e_Y+1/2)+1/2$. Slack is at least $1/16$. A downward angular jump gives the square difference plus $2(e_Y+1/2)+1/2$, hence at least $1/2$. The other terms have nonnegative combined primary defect. Every block therefore has nonnegative defect for large $H$.

For three points in a product energy shell of exponentially small width $W$ the sum of defects is at most $2W$. Thus there are no carries, crossed cuts, or angular jumps. For each block the midpoint is the actual mean in $(s,e)$, the two endpoints are on the same sheet, $w$ is affine on their primary segment, and $|e_X-e_Z|=O(\sqrt W)$, $d_s=O(\sqrt{W/K})$. For these last bounds the angular square gives its exact nonnegative square difference and $\Delta\Phi\ge(1-\lambda/2)d_s^2$. The assertion about angular sheets concerns the endpoints; the middle can have two angular lifts above the seam.

## Ellipsoid and the second endpoint

For $z=(s_X-s_Z,e_X-e_Z)$ the local defect is at least $(1-O(\sqrt W))z^\mathsf{T}M_Xz/2$, uniformly, where
$$
 M_X=\operatorname{diag}(2K,1)+\frac{\lambda K}{D_X}
           (w',w/D_X)^\mathsf{T}(w',w/D_X).
$$
Indeed for affine $w,D$ the exact perspective defect is $D_X(w' z_1+(w_X/D_X)z_2)^2/[D_Z(D_X+D_Z)]$ with equality before the other energy terms are added. The ratio to its leading coefficient differs from one by $O(\sqrt W)$. On the inactive band the matrix is exactly diagonal. We can lower bound $\log(4\sqrt{\det M_X})$ by
$$
 T(X)=\log(4\sqrt2 H)+\boldsymbol1_{w>0}\log^+(H\sqrt\lambda\, w/D^{3/2})
$$
by retaining the baseline and the angular part of the rank-one update in the determinant.

At fixed first endpoint $X$, the physical common-step measure corresponding to the endpoint-difference variable in each block is at most $dz/4$. In fact the final endpoint on the first endpoint's sheet is uniquely specified by $z$, with angular Jacobian $1/p$, $p=1$ below and $2$ above. Each of the four torus half-step branches has an additional Jacobian $1/4$. The middle primary coordinate is its unique ordinary choice. Below the seam only one angular half-step can be in the middle interval of width $\le1/2$, and above the seam there are at most two. This proves the claimed upper bound on admissible branch measure for both layers.

Choose a fixed open rectangle of positive area compactly inside an inactive sheet. Call a product first endpoint typical if it has a coordinate in this rectangle and its average $T$ is at least $\mathbb ET-m^{-1/4}$. Endpoints are sampled independently under uniform trimmed area. The complement has probability $O((\log m)^2/\sqrt m)+O(e^{-c_1m})$ by Chebyshev, since $T=O(\log m)$, and the rectangle's uniformly positive probability. For the marked coordinate, the final endpoint is exponentially close and remains in the same inactive sheet away from all edges and cuts. For fixed final $e$ there the derivative in $s$ of $F$ is at least $K$, because $4s-L>1$ and both hinge contributions have nonnegative slope. The prescribed product shell for the **final** endpoint thus restricts its marked $s$ coordinate, conditional on all the others, to length at most $W/K$. This argument holds separately for each possible $z$ slice; monotonicity holds on the whole local rectangle.

Put $R_W^2=4W(1+O(\sqrt W))$. The product ellipsoid is the ball of radius $R_W$ after the transformations by $M_X^{1/2}$. The marked primary variable has scaling $\sqrt{2K}$ with no off-diagonal term. Fubini bounds admissible ball volume by the central $(2m-1)$-ball volume times the scaled slice length $\sqrt{2K} W/K$. Relative to the full ball this is at most $C\sqrt{mW/K}$ using the consecutive ball-volume ratio $O(\sqrt m)/R_W$. With the Jacobians, the conditional common-step measure is therefore at most
$$
 C\sqrt{mW/K}\;\frac{\pi^m R_W^{2m}}{m!}
      \exp[-m(\mathbb E T-m^{-1/4})].
$$
This factor uses membership in a fixed energy interval; imposing only a bound on the total midpoint defect would give the full ball.

## Shell mass and coefficient

Write $a_0=\log(1/A)$ and take $m$ nearest to $\sqrt{\log N/a_0}$. Under uniform area on the untrimmed block set $\sigma^2=\operatorname{Var}(\Phi)>0$. Positive variance follows already on the chosen inactive rectangle. The normalized energy $F/K$ is uniformly bounded and converges in distribution with variance converging to $\sigma^2$ by the area estimate and the uniformly negligible extra terms. For the sum of iid trimmed energies, Berry–Esseen on a central slab of half-width $m^{-1/12}$ standard deviations gives mass $(1+o(1))2m^{-1/12}/\sqrt{2\pi}$. Discarding atypical points costs $o(m^{-1/12})$. Partitioning the slab into intervals of width $W$, extending its final interval if necessary, finds a shell of typical points of measure at least
$$
 (1-o(1)) |T_H|^m W/(K\sigma\sqrt{2\pi m}).
$$
Use the enlarged width
$$
 W=(1-m^{-1/4}) A^{-1/2}\frac{m}{4\pi\mathrm e}
         \exp(\mathbb E T-m^{-1/4})N^{-1/m}.
$$
We have $\log W=-a_0m+O(\log m)$ from the dimension choice and $T=O(\log m)$. Thus $\sqrt W$ in the slice estimate cancels the factor $A^{-m/2}$ from widening the ellipsoid. The remaining polynomial factors times $(1-m^{-1/4})^m$ tend to zero. The conditional common-step measure is $o(1/N)$ by $m!\ge(m/\mathrm e)^m$. For a uniform torus direction and independent translate, each first endpoint is Haar independent of every fixed positive multiple of the direction, which is also Haar. Subtracting one point per increasing progression by the first moment argument gives a progression-free subset of $[1,N]$ of size at least $(1-o(1))N$ times the shell measure.

Under uniform area on $S$ let
$$
 \mu=\log(4\sqrt2)+\mathbb E_S[\boldsymbol1_{w>0}(\log w+\tfrac12\log\lambda-\tfrac32\log D)].
$$
The log singularities are integrable, as is also seen from the explicit integral below. The trimmed active fraction differs from $\theta$ by $O(1/H)$. After subtracting its log-$H$ term on each active coordinate, the clipped logarithm defining $T$ is bounded above by a constant and below by $\log w-O(1)$. Dominated convergence gives $\mathbb E T=(1+\theta)\log H+\mu+o(1)$. The resulting coefficient, taking $c=\kappa/B_0$ to maximize the scale factor, is at least
$$
 \frac{a_0^{-\beta_*}\exp(\mu-\rho)c^{-\rho}}
 {\sqrt A\,4\pi\mathrm e\sqrt{2\pi}\,\sigma}.
$$
Indeed $|T_H|^m/A^m\to\exp(-\kappa/(Ac))$, $m^{\theta-1/2}\sim(\log N/a_0)^{\beta_*}$, and integer rounding changes the leading exponential by $1+o(1)$.

## Certified numerical comparison

The lower width is $1/2-b(R-s)_+$, the plateau strip has width $1/2$, and above $V$ the width is $2b(R-u)-b(G-u)_+$. Thus the integral of $\log w$ over the active set equals
$$
 \int_0^{1/2}(1/2-b(R-s)_+)\log(1/2-s)\,ds
 +\tfrac12(V-J)[\log(V-J)-3\log2-1]
 +\int_V^R [2b(R-u)-b(G-u)_+]\log(u-V)\,du .
$$
The middle term sums $a_i(\log(a_i/2)-1)/2$ over the dyadic lengths. Jensen's inequality bounds the conditional mean log denominator by the log of the conditional mean denominator. The latter is enclosed by affine angular integrations on each original sheet outside the plateaus, using the upper bound two on the plateaus. For variance use $\sigma^2\le\mathbb E[(\Phi-37/100)^2]$, enclosing $P$ between $w^2/2$ and $w^2$ and $C(s)$ between $2(V-J)(s-1/2-V)_+$ and $2(V-J)(s-1/2-J)_+$. Primary partition cells do not cross the breakpoints of these bounds. Interval evaluation on 256 subdivisions per band gives $\sigma<0.328414$, a conditional mean denominator below $1.558367$, and a directed **lower comparison** exceeding $0.0244079$. This proves the announced strict numerical inequality. These bounds need not approximate the best coefficient of this construction.

Run `python3 endpoint_constant.py /path/to/erdos142-deterministic-shell 256` with mpmath, using the [pinned original polygon modules](https://github.com/Deldor14/open-math-agents/tree/7cfb0d9031b6d43fbf110d0b131b65c349b43033/research/erdos142-deterministic-shell). The four Lean lemmas in `EndpointTents.lean` isolate the tent payment, upward square, lower carry and contact margin. The complete geometric and probabilistic argument is written above. The result is an existential lower bound, with the exact asymptotic for the interval extremal function still open.
