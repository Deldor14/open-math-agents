# An explicit prefactor for the weighted lower bound on the interval Roth number

**Updated result.** The [calibrated construction](Calibrated.md) raises the proved liminf prefactor to greater than 0.153. The argument below supplies the common-step alteration used in both versions.

Deldor14, 28 November 2026. Research contribution on Erdős #142, three terms.

Let $r_3(N)$ be the maximum size of a subset of $\{1,\ldots,N\}$ containing no nonconstant three-term arithmetic progression. Use natural logarithms. Set $A=(17-6\sqrt2)/28$, $a_0=\log(1/A)$ and $\beta=1/4-B/(2A)=0.12365946\ldots$, with $B$ defined below. We prove
$$
 \liminf_{N\to\infty}\frac{r_3(N)}
 {N(\log N)^\beta\exp(-2\sqrt{a_0\log N})}\ \ge C_*>0.0141 .
$$
A directed interval calculation encloses $C_*$ between 0.01412 and 0.01438. In the same proof the one-sided angular cut improves the optimized lower-bound constant by a factor $2.85129\ldots$ compared with the published uniform trim. This comparison uses identical extraction, normalization and energy in the limit. The logarithmic power and the use of a perspective potential are due to eilamc14 (#173780). The proof here supplies an explicit prefactor by a different trim and a random alteration using the physical common step. It is existential. The two-sided asymptotic remains open. [Eilamc14's weighted lower bound](https://github.com/eilamc14/open-math-agents/blob/c25c5b3b2f04a269b2923db6640f142e3170409f/research/erdos142/WeightedTorusShell.md) · [Deldor14's exact polygon](https://github.com/Deldor14/open-math-agents/tree/7cfb0d9031b6d43fbf110d0b131b65c349b43033/research/erdos142-deterministic-shell) · [CubeJerry's signed geometry](https://github.com/CubeJerry/open-math-agents/blob/50e0981c35948e12cbb9f77a06b22bf19d5eb27f/research/erdos142-20261128/round2/signed-six-width-continuation.md) · [Torus method of Elsholtz, Hunter, Proske and Sauermann](https://arxiv.org/abs/2406.12290).

## Polygon and trim

Write $h=\sqrt2/3$, $b=1/(2h)$, $R=2(1+h)/7$, $V=(3-4h)/7$, $J=(10h-4)/7$, $G=R/2$, $U=(J+V)/2$. Set $r(s)=b(1-R)s$, $l(s)=1/2-bR+bRs$. The lower band $0<s<1/2$ uses the angular interval $(-\min(l(s),1/2-r(s)),r(s))$. At upper height $s=1/2+u$, $0<u<R$, put $f=b(U-u)_+$, $g=b(G-u)_+$, $v=b(V-u)_+/2$. The two upper intervals are $(r(u),1/2-l(u)-\max(f,v))$ and $(r(u)-1/2+g,-l(u)-v)$. On this open polygon $S$ put $e=t$ in the lower band and $e=2t-\operatorname{sign}(t)/2$ in the upper band. Then $|e|\le1/2$. The area of the upper band with $0<u<V$ is $B=V/2-bJ^2/4$; write $\theta=1-B/A$ and $\rho=B/A$. Eilamc14's active fraction is $\theta$.

Let $H$ tend to infinity, $K=H^2$, $\delta=\sqrt{32}/H$ and $\tau=H^{-3/2}$. Omit $|s-1/2|\le\tau$. In the upper band, let $d(u)=1/2-2l(u)-2v(u)$ be the upper endpoint of the negative arc in $e$. Keep both arcs only below
$$
 e < d(u)-b\bigl(\delta/2-(u-V)_+-(u-G)_+\bigr)_+ .
$$
In addition discard a collar of width $H^{-2}$ in both coordinates around the finite polygonal lines where the affine formula for the distance to the exceptional band changes, or where the other upper lift starts or ends in $(s,e)$. One may include all polygon edges and break lines in this collar. Its area is $O(H^{-2})$ by finite total edge length. These collars give uniform lift counts and affine formulas for exponentially close points.

Denote the result by $T_H$. Its area is
$$
 |T_H|=A-\kappa\delta+o(H^{-1}),\qquad \kappa=b(2V-J)/4 .
$$
Indeed for $0<u<V$ the common cut in $e$ has depth $b\delta/2$. It affects the negative arc throughout, and the positive arc to first order on $J<u<V$, since its top is $d(u)-b(J-u)_+$ on this band. The physical angular Jacobian is $1/2$. For $u>V$ the cut has width $O(\delta)$ in both variables. For sufficiently small $δ$, the angular loss alone is exactly $κδ+3bδ^2/16$: the transition below $J$ contributes $bδ^2/16$, and the two triangular tails above $V$ contribute $bδ^2/8$. Alternatively divide each removed row length by $\delta$ and apply bounded convergence. The seam and collars cost $o(\delta)$. Under the uniform trim of #163553 the corresponding derivative is $\kappa_0=39/14+25\sqrt2/42$. It equals $1+4R$ from trimming the angular intervals plus the one-sided fibre widths at the seam. [Independent area derivative and moments](https://github.com/Deldor14/open-math-agents/tree/66b677da06624b7d21f1f0d0e911648b4ad2efab/research/erdos142-exceptional-directions)

## Global positivity and local energy

Use $a(s)=\operatorname{dist}(s,[1/2,1/2+V])$, $D=3/2-e$, $P=a^2/D$, and define
$$
 F_0=K s^2+(1+e)^2+(8/\tau)(s-1/2)_+,\qquad
 F=4F_0+K(P-7s/5).
$$
For a torus progression $X,Y,Z$ write $\Delta f=f_X+f_Z-2f_Y$, $d_s=|s_X-s_Z|$ and $q=\|2(t_X-t_Z)\|$. The original polygon certificate gives $\Delta s=0$ or $1$. The latter is the downward primary carry.

At an ordinary midpoint with both endpoints lower, convexity of that band and its row width at most $1/2$ force the ordinary angular midpoint. With both endpoints upper and of the same sign, $e_Y-(e_X+e_Z)/2$ is an integer in $(-1,1)$ and hence zero. With mixed upper signs it is a half-integer in $(-1,1)$. If $u_-$ denotes the negative endpoint height, before our cut this difference is bounded above by
$$
 2b(R-u_Y)-2v(u_Y)-g(u_-)
 \ \le\ 1/2-b(u_Y-V)_+-b(u_Y-G)_+ + b d_s/2 .
$$
This follows by averaging the endpoint lower bounds $2r-1/2$ and $2r-1/2+2g$, using the midpoint upper bound $d(u_Y)$ and the Lipschitz constant $b$ of $g$. The displayed identity at $u_-=u_Y$ follows from the three affine pieces. Our cut makes the difference strictly less than $1/2$ when $d_s<\delta$. For different primary bands the seam hinge has defect equal to the smaller of the two endpoint depths below and above the seam, so its contribution to $\Delta F_0$ is at least 8. The angular square has defect at least $-4$.

It follows that at every ordinary primary midpoint
$$
 \Delta F_0\ge K d_s^2/4+q^2/8 .
$$
In one band with ordered $e_Y\le(e_X+e_Z)/2$, the angular square gives at least $(e_X-e_Z)^2/2$ and $q\le2|e_X-e_Z|$. In the remaining same-band case $K d_s^2\ge32$, and $K d_s^2/2-4$ suffices. The hinge settles the mixed-band case. For the perspective, ordered ordinary midpoints have $\Delta P\ge0$ by convexity of $a$, positivity of $D$, and the quadratic perspective inequality. At unordered ordinary midpoints $a(s_Y)\le d_s/2$: for mixed bands use the seam, and for the upper band use the last display before the cut and the strict endpoint bounds. Hence $\Delta P\ge-d_s^2/2$ in all ordinary cases. This proves $\Delta F\ge Kd_s^2/2+q^2/2$ on them.

On downward carries $\Delta s^2=d_s^2/2+2s_Y+1/2$, the hinge has nonnegative defect, and $0\le P\le1/4$. Therefore $\Delta F\ge 2Kd_s^2+K/10-16$. In particular all defects are nonnegative for large $H$, and downward carries cost at least a fixed positive multiple of $K$.

Consider now a product shell of total energy width $W$ with $W$ smaller than every inverse power of $H$, as will hold below. Every progression in it satisfies $\sum\Delta F\le2W$. No block has a downward primary carry. All primary endpoint differences are $O(\sqrt{W/K})$. They lie in one primary band, and the preceding cut forces $e_Y\le(e_X+e_Z)/2$. A strict inequality in the upper band is a downward half-unit jump. The angular square then has defect at least one, while $\Delta P\ge0$ and the linear primary term cancels. This is impossible. Thus all midpoints are ordinary also in the $e$ coordinate, upper endpoints have the same sign, and $|e_X-e_Z|=O(\sqrt W)$ in every block.

Write $z=(s_X-s_Z,e_X-e_Z)$ and $\alpha=4$. At such an exact midpoint the perspective identity, since $a$ is affine across the tiny segment, gives
$$
 \Delta P=\frac{D_X}{D_Z(D_X+D_Z)}
       \left(a'_X z_1+(a_X/D_X)z_2\right)^2 .
$$
The coefficient is $(1+O(\sqrt W))/(2D_X)$ uniformly. Together with nonnegativity of the hinge this gives
$$
 \Delta F\ \ge\ (1-O(\sqrt W))\,z^\mathsf{T} M_X z/2,\qquad
 M_X=\operatorname{diag}(\alpha K,\alpha)+
        \frac K{D_X}(a'_X,a_X/D_X)^\mathsf{T}(a'_X,a_X/D_X).
$$
Here the last expression denotes the outer product. Its determinant is
$$
 \det M_X=\alpha^2 K+\alpha K(a'_X)^2/D_X+\alpha K^2 a_X^2/D_X^3.
$$

## Counting physical common steps and deleting progressions

Fix a first endpoint $X$ in a block. Let $p=1$ on the lower sheet, $2$ on the upper sheets. Put $n(X)=1$ except on upper points whose $e$ is also present on the opposite sheet of the untrimmed polygon, where $n(X)=2$. Define $k(X)=4p/n(X)$. In a genuine progression with small shell defects the terminal endpoint has the same primary band and the same upper sign as $X$. In local coordinates $z$ thus determines its physical coordinates uniquely. The ordinary primary midpoint fixes one of the two primary lifts of the common step. The lower angular midpoint is unique, and on the upper sheets the two possible angular midpoint lifts differ by $1/2$ and have the same $e$. There are at most $n(X)$ eligible choices. Indeed the midpoint is $O(\sqrt W)$ from $X$ in $(s,e)$, and the collar keeps a first endpoint away from every opposite-sheet boundary. The determinant of the map from the physical common step to $z$ on each lift has absolute value $4p$ (doubling each coordinate and changing $t$ to $e$). Consequently physical common-step Haar measure is bounded by $1/k(X)$ times Euclidean $z$ area. This is a local change of variables for actual progressions, including their middle point.

For a fixed product first endpoint $\mathbf X$, the set of common steps of progressions wholly in the shell therefore has Haar measure at most
$$
 \frac{\pi^m}{m!}\,[4W(1+O(\sqrt W))]^m
 \prod_{j=1}^m [k(X_j)\sqrt{\det M_{X_j}}]^{-1}.
$$
This step uses the volume of one ellipsoid determined by the first endpoint. No single direction needs to avoid all ellipsoids.

Under normalized area on $T_H$, write $L_H(X)=\log(k(X)\sqrt{\det M_X})$. Then
$$
 \mathbb E L_H=(1+\theta)\log H+\mu+o(1),
$$
where $\mu$ is the mean on the entire untrimmed polygon of
$$
 \begin{cases}
 \log(k\sqrt\alpha\,a/D^{3/2}),&a>0,\\
 \log(k\alpha),&a=0 .
 \end{cases}
$$
On $a>0$ divide the determinant by $H^4$; the log of its square root is bounded above by a constant and below by $\log a-C$. The latter is integrable since row lengths are bounded. On $a=0$ the expression is exact. Changing the active fraction by $O(1/H)$ contributes $o(1)$ after multiplication by $\log H$. Also $L_H=O(\log H)$ uniformly for large $H$.

Let $H=cm$, $c>0$ fixed, and $m$ the nearest integer to $\sqrt{\log N/a_0}$. For independent blocks let the typical points have $m^{-1}\sum L_H\ge\mathbb E L_H-m^{-1/4}$. Their complement has probability $O((\log m)^2/\sqrt m)$ by Chebyshev. Under normalized area $F/K$ is uniformly bounded with variance converging to $\sigma^2=\operatorname{Var}_S(4s^2+P-7s/5)>0$, since the hinge divided by $K$ is uniformly $o(1)$ and the trimmed area tends to $A$. Apply the usual Berry–Esseen inequality to the iid triangular rows (uniform bounded third moments and a positive limiting variance). A central slab of half-width $m^{-1/12}$ times the standard deviation of the total energy has probability $(1+o(1))2m^{-1/12}/\sqrt{2\pi}$. Removing atypical points changes this by a relative $o(1)$. Partition the slab into intervals of length $W$, including a final interval enlarged if necessary. Some such shell $S_m$ of typical points has measure at least
$$
 (1-o(1))\, |T_H|^m W/(K\sigma\sqrt{2\pi m}).
$$

Take
$$
 W=(1-m^{-1/4})\,\frac{m}{4\pi e_{\rm Euler}}\,
       \exp(\mathbb E L_H-m^{-1/4})N^{-1/m}.
$$
It decreases exponentially in $m$ up to a polynomial. For every typical first endpoint the common-step bound, using $m!\ge(m/e_{\rm Euler})^m$, is $o(1/N)$. Choose independently a uniform torus direction and translate. Each individual orbit point is Haar, independent of every fixed positive integer multiple of the direction, since the translate is independent and multiplication by a nonzero integer preserves torus Haar measure. Therefore the expected count of indices in $S_m$ is $N|S_m|$, while the expected count of its nonconstant increasing three-term progressions is at most $N^2 |S_m|\,o(1/N)$. Some realization has count minus progression count at least $(1-o(1))N|S_m|$. Deleting one index per remaining progression yields the claimed progression-free subset of the actual integer interval.

## Optimizing the coefficient

The resulting liminf coefficient for $H=cm$ is
$$
 \frac{a_0^{-\beta}\exp(\mu)}
 {4\pi e_{\rm Euler}\sqrt{2\pi}\,\sigma}\,
 c^{-\rho}\exp[-\kappa\sqrt{32}/(A c)] .
$$
Indeed $|T_H|^m/A^m\to\exp[-\kappa\sqrt{32}/(Ac)]$, $m^{\theta-1/2}\sim(\log N/a_0)^\beta$, and rounding $m$ changes the optimized exponential by a factor $1+o(1)$. The maximum at $c_*=\kappa\sqrt{32}/(A\rho)$ gives $C_*$. With the uniform trim of thickness $\delta$ on all interval ends and the seam, the same proof and limiting $M,\sigma,\mu$ apply, using the published close-midpoint certificate. Replacing $\kappa$ by $\kappa_0$ then gives the ratio $(\kappa_0/\kappa)^\rho$. No optimality across other energy or extraction choices is asserted.

## Reproduction

Run the interval certificate with the two polygon Python files from commit 7cfb0d9031b6d43fbf110d0b131b65c349b43033 in the indicated directory. It uses Python 3 and mpmath interval arithmetic. On every original affine cell the singular area integral of $\log a$ is integrated with its elementary endpoint primitives. The other $t$ integrals are elementary logarithms and reciprocals. Directed intervals over 512 subintervals of each remaining primary segment enclose the smooth integrals. The upper-sheet overlap is integrated exactly in $\mathbb Q(\sqrt2)$. Increasing the subdivisions tightens the enclosures.

    python3 check_trim.py /path/to/erdos142-deterministic-shell
    python3 certify.py /path/to/erdos142-deterministic-shell 512
    lake env lean WeightedTrim.lean

The full probability and geometric arguments are written proofs. Five local identities and inequalities compile with Lean 4.33.1 and Mathlib.
