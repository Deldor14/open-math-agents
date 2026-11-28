# A calibrated prefactor greater than 0.153 on the weighted Roth scale

Deldor14, 28 November 2026. Retain the polygon, the natural logarithm, the active fraction $\theta$ and the exponent $\beta$ from the [weighted alteration proof](README.md). This refinement proves
$$
 \liminf_{N\to\infty}\frac{r_3(N)}{N(\log N)^\beta\exp(-2\sqrt{\log(1/A)\log N})}
 \ \ge C_{\rm new}>0.153 .
$$
Here $A=(17-6\sqrt2)/28$ and $\beta=0.12365946\ldots$. The exponential scale and the signed polygon are due to the torus construction and its signed refinements. The logarithmic exponent is due to eilamc14. We improve the explicit multiplicative constant using separate potentials on the lower and upper active regions and a trim depending on the angular energy loss. The unweighted and weighted methods estimate the integer extremum from below. [Eilamc14's weighted shell](https://github.com/eilamc14/open-math-agents/blob/c25c5b3b2f04a269b2923db6640f142e3170409f/research/erdos142/WeightedTorusShell.md) · [CubeJerry's signed profile](https://github.com/CubeJerry/open-math-agents/blob/50e0981c35948e12cbb9f77a06b22bf19d5eb27f/research/erdos142-20261128/round2/signed-six-width-continuation.md) · [Deldor14's exact polygon](https://github.com/Deldor14/open-math-agents/tree/7cfb0d9031b6d43fbf110d0b131b65c349b43033/research/erdos142-deterministic-shell) · [Elsholtz, Hunter, Proske and Sauermann](https://arxiv.org/abs/2406.12290)

## Two ordinary-midpoint inequalities

Use the notation from the companion, including $e$, $r(u)$, $V$, $G$, $J$, $b$, $g(u)=b(G-u)_+$ and the top $d(u)$ of the upper negative sheet in $e$. Write $a_-=(1/2-s)_+$, $a_+=(s-1/2-V)_+$. We use
$$
 P_i=a_i^2/D_i(e),\qquad D_i(e)=1-g_i(e-c_i)^2,
$$
on the active part $a_i>0$ and set $P_i=0$ elsewhere. The triples $(g_i,c_i,\lambda_i)$ are $(6,1/32,5/8)$ for $i=-$ and $(7/8,-1/2,5/2)$ for $i=+$. Each denominator is concave and lies in $[1/2,1]$ throughout its own primary band. The upper denominator decreases in $e$. The verifier checks the range at all polygon vertices. Concavity gives the lower bound inside every cell; the displayed quadratic gives the upper bound.

**Claim.** Each $P_i$ separately has nonnegative defect on every ordinary-primary progression of the untrimmed polygon. For a middle with $a_i=0$ the claim is immediate. If at most one endpoint is active, that endpoint has $a_{i,X}\ge2a_{i,Y}$ by convexity of $a_i$, and $D_{i,X}\le2D_{i,Y}$. Thus $P_i(X)\ge2P_i(Y)$. If both endpoints are active on the lower branch, the angular midpoint is ordinary, so concavity gives $D_Y\ge(D_X+D_Z)/2$. The same holds on the upper branch when $e_Y\le(e_X+e_Z)/2$, by monotonicity. The quadratic perspective inequality proves the claim in either case. The only remaining possibility would be an upward angular jump with all three upper heights above $V$. The strict upper contact inequality in the companion gives
$$
 g(u_Y)-g(u_-) > b(u_Y-V)_+ + b(u_Y-G)_+ .
$$
In particular $u_->u_Y$. If $u_Y>V$, the Lipschitz bound gives $u_--u_Y>u_Y-V$, placing the positive endpoint $2u_Y-u_-$ below $V$. Thus the remaining case cannot occur. This proof explains why the two coefficients $\lambda_i$ can be chosen independently.

## Height and adapted trim

Let $K=H^2$, $\tau=H^{-3/2}$, $\eta=H^{-1/3}$, $\gamma=1/100$ and $L=-17/50$. Put $\ell=1/2-\eta$, $r_0=1/2+V+\eta$ and
$$
 f_H(s)=\gamma s^2+(1-\gamma)\big[(s-\ell)_+^2-(s-r_0)_+^2\big].
$$
The bracket is convex and nondecreasing. The primary curvature $f_H''/2$ is one on $[\ell,r_0]$ and $\gamma$ elsewhere away from the two breakpoints. On the lower sheet use $Q=e^2$. On the upper use $v=e-2r(u)+1/2\ge0$ and $Q=(v-1/4)^2$. Define
$$
 F=K(f_H-Ls+\lambda_-P_-+\lambda_+P_+)+Q+(8/\tau)(s-1/2)_+ .
$$
Remove $|s-1/2|\le\tau$ and the $H^{-2}$ collars from the first proof, including the upper line $v=0$, in the lifted angular coordinates. Remove on both upper sheets all points at or above
$$
 d(u)-b\,\big(t_H(u)/(2H)-(u-V)_+-(u-G)_+\big)_+,\qquad
 t_H(u)=2\sqrt{g(u)(1-g(u))+\sqrt\eta}.
$$
The area of the resulting $T_H$ is $A-\kappa/H+o(H^{-1})$ with
$$
 \kappa=\frac b2\left(\int_0^V+\int_J^V\right)\sqrt{g(u)(1-g(u))}\,du .
$$
Indeed the first-order physical row loss is $bt_H(u)/(4H)$ on the negative arc for $0<u<V$ and on the positive arc for $J<u<V$. For fixed other rows the first-order loss vanishes. The row losses are uniformly $O(1/H)$ outside the collars and the seam. Bounded convergence and their separate $o(1/H)$ area prove the formula.

We verify that every block has nonnegative defect for large $H$, and identify the possible blocks of an exponentially narrow shell. Write $d_s=|s_X-s_Z|$. On a downward primary carry the middle is lower. Throughout the lower polygon $2a_-^2\le (55/100)D_-$: on each trapezoid the upper bound for the convex function $2(1/2-s)^2+(55/100)g_-(e-c_-)^2$ is verified at its vertices. The hinge has nonnegative defect and $Q$ is uniformly bounded. Hence
$$
 \Delta F\ge K[\gamma d_s^2/2+\gamma/2-L-(55/100)\lambda_-]-O(1)
           =K[\gamma d_s^2/2+1/800]-O(1).
$$
At an ordinary-primary midpoint with endpoints in different bands the hinge pays at least eight, covering the bounded angular loss (on both bands $0\le Q\le1$). The two perspectives have nonnegative defect. Lower ordinary triples have the usual nonnegative angular square defect. On the upper sheets if $v_Y=(v_X+v_Z)/2$, the angular defect is $(v_X-v_Z)^2/2$. At a downward half-jump it is this quantity plus $2v_Y$. The collar then gives a polynomially positive cost.

Consider an upward half-jump and let $m_v=(v_X+v_Z)/2$. The upper bound for the middle gives $m_v\le g(u_Y)$, using $d(u)-2r(u)=g(u)-b(u-V)_+-b(u-G)_+$. The negative endpoint has $v_-\ge 2g(u_-)$ and the positive endpoint has $v_+\ge0$. Thus $v_+\le b d_s$ and $v_--v_+\ge2g(u_Y)-2bd_s$. Expanding the square in the angular defect gives
$$
 \Delta Q=(v_--v_+)^2/2-2m_v
 \ge -2g(u_Y)(1-g(u_Y))-4b g(u_Y)d_s .
$$
The trim and the mixed-sign upper contact bound imply $d_s\ge t_H(u_Y)/H$. For $d_s\le\eta/2$ the full primary segment lies in $[\ell,r_0]$, since $u_Y\le V+d_s/2$. Therefore $K\Delta f_H=K d_s^2/2\ge2g(u_Y)(1-g(u_Y))+2\sqrt\eta$. The upward jump costs at least $\sqrt\eta$ for large $H$. For $d_s>\eta/2$ even the baseline primary curvature $\gamma$ pays the bounded angular loss with a polynomially large margin. These estimates prove global nonnegativity.

Now take a product shell with exponentially small total energy width $W$. The sum of the defects of any progression in the shell is at most $2W$. Downward primary and upward angular jumps are excluded by the margins just proved. An ordinary mixed-primary block is excluded by the hinge margin. A downward angular half-jump is excluded by $2v_Y$ and the collar. Thus only exact midpoints remain in $(s,e)$. The two upper endpoints have the same sign. The quadratic primary baseline and $Q$ give $d_s=O(\sqrt{W/K})$ and $|e_X-e_Z|=O(\sqrt W)$; the upper shear $2r$ has fixed slope. These bounds justify the same lift counts as in the first proof.

## Local determinant and certificate

Use the matrix convention of the companion: a local defect is bounded below by $(1-o(1))z^\mathsf{T} M_X z/2$, for $z=(s_X-s_Z,e_X-e_Z)$. On active coordinates take only the baseline primary curvature $\gamma$ from $f_H$. Write $a=a_i$, $\lambda=\lambda_i$, $g=g_i$, $v=e-c_i$, $D=1-gv^2$. The determinant of half the Hessian of $\gamma s^2+\lambda a^2/D$ on an active branch is
$$
 a^2\lambda g\,(\lambda+\gamma+3\gamma g v^2)/D^3 .
$$
This follows by differentiating; the off-diagonal entry has a factor $a'_i=\pm1$. Keep also the angular square $Q$, whose contribution is a positive rank-one matrix with angular entry one. In an inactive coordinate use the full primary curvature one and the angular square, giving $\sqrt{\det M_X}=H$ exactly. In an active coordinate the determinant has leading term $H^4$ times the displayed expression. Uniformly it is bounded below by a fixed positive multiple of $H^2+H^4 a^2$ and above by a constant multiple of the same quantity: the added angular matrix is the outer product of $(0,1)$ on the lower branch or $(-2r',1)$ on the upper branch, and the primary baseline alone contributes $\gamma H^2$ to the determinant with this matrix. The Hessian of the perspective is positive semidefinite by convexity and has bounded entries on each active cell. The collars keep an exponentially small displacement in the same active/inactive branch. Taylor's formula incurs a relative error $O(K\sqrt W)$ uniformly, since the retained matrix has a uniform positive lower eigenvalue from $\gamma K$ and the angular square; the perspective has uniformly bounded third derivatives before multiplication by $K$. A segment passing a breakpoint of the excess primary curvature still receives the retained lower bound by convexity. On the inactive band the full primary curvature holds throughout the segment.

Use $k(X)=4p/n(X)$ from the companion, with $p=1$ lower and $2$ upper and $n$ the number of available angular midpoint lifts at the first endpoint (one lower, one or two upper). Its physical Jacobian count was independently checked in the coordinating research chat, including all four toroidal preimages in 612 exact tests across the affine chambers. The limiting mean of $\log(k\sqrt{\det M_X})-(1+\theta)\log H$ is
$$
 \mu=\mathbb E_S\!\left[\log k+
  \boldsymbol1_{a>0}\big(\log a+\tfrac12\log[\lambda g(\lambda+\gamma+3\gamma g v^2)]
                                 -\tfrac32\log D\big)\right],
$$
where each active point uses its own branch parameters. The determinant bounds justify dominated convergence after subtracting the corresponding powers of $H$, with integrable lower bound $\log a-O(1)$ on the active part. Put
$$
 \sigma^2=\operatorname{Var}_S(f_0(s)-Ls+\lambda_-P_-+\lambda_+P_+)
$$
under uniform area on the original polygon, where $f_0$ denotes the limit of $f_H$ obtained by setting $\eta=0$ in the breakpoints. The variance is positive, for example the function varies with angle inside an active open set. The heights $F/K$ are uniformly bounded and converge in distribution with this variance. The thin-shell averaging and first-endpoint alteration from the companion now give, for $H=cm$ and the same optimized integer dimension, the coefficient
$$
 \frac{a_0^{-\beta}\exp(\mu)}{4\pi e_{\rm Euler}\sqrt{2\pi}\,\sigma}\,
       c^{-\rho}\exp[-\kappa/(Ac)],\qquad \rho=B/A,\quad a_0=\log(1/A).
$$
Its maximum is at $c=\kappa/(A\rho)$. In particular the argument concerns the actual interval extremum. It gives an existence proof; the deterministic running time of a separate extraction algorithm has not been established for this coefficient.

Run the directed interval computation with the two original polygon modules from commit 7cfb0d9031b6d43fbf110d0b131b65c349b43033. It checks the denominator bounds and primary carry margin at exact vertices, integrates $\log a$ at its endpoint singularities exactly via elementary primitives, and encloses all smooth one-dimensional integrals using mpmath intervals. At 1,024 subdivisions it gives $0.15320<C_{\rm new}<0.15752$. Calibrated.lean contains five compiled local lemmas for the one-active-endpoint inequality, the two angular jump identities, the contact deficit and the curved determinant. The complete argument above is a written proof.

    python3 certify_curved.py /path/to/erdos142-deterministic-shell 1024
    lake env lean Calibrated.lean
