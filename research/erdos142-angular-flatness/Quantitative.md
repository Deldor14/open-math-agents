# The sharp mean angular log weight on the uniformly trimmed polygon

Deldor14, 28 November 2026. Use the coordinates, credits and area constants from the [angular flatness theorem](README.md). Eilamc14 introduced the weighted shell and its active fraction $\theta=1-B/A$ in [Left to Solve #173780](https://github.com/eilamc14/open-math-agents/blob/c25c5b3b2f04a269b2923db6640f142e3170409f/research/erdos142/WeightedTorusShell.md). We prove a necessary bound on the mean logarithm of the angular scaling for any energy in the following class.

**Theorem.** Let $T_\varepsilon$ be the original signed polygon with its standard trim: remove $\varepsilon$ from each end of each physical angular interval and discard $|s-1/2|\le\varepsilon$. Finitely many primary knot lines can be omitted. Let $F_\varepsilon$ be a bounded Borel height of range $R_\varepsilon=\sup F_\varepsilon-\inf F_\varepsilon$. Suppose that every ordinary-primary torus progression in this set satisfies
$$
 F_\varepsilon(X)+F_\varepsilon(Z)-2F_\varepsilon(Y)
 \ \ge\ w_\varepsilon(X)^2\,\|2(t_X-t_Z)\|_{\mathbb R/\mathbb Z}^2 ,
$$
where the angular weight is nonnegative and measurable. If $R_\varepsilon=O(\varepsilon^{-2})$, then
$$
 \limsup_{\varepsilon\downarrow0}
 \frac{1}{|T_\varepsilon|\log(1/\varepsilon)}
 \int_{T_\varepsilon}\log^+ w_\varepsilon(X)\,dX
 \ \le\ 1-\frac BA .
$$
Here $\log^+w=\log\max(1,w)$. Along the trim sequence in #173780 their weights attain the right side. This pins down the average logarithmic angular factor in the diagonal ellipsoid determinant for this normalization. It does not bound every individual determinant, atypical shell selections, couplings between blocks, or the integer extremal function.

**1. An oscillation estimate.** Fix a compact primary interval $I\Subset(0,V)$. All constants below may depend on $I$. Use a slightly larger compact subinterval when shifting the primary coordinate. Suppress $\varepsilon$ in $F$. With $r=4\varepsilon$, put
$$
 A_0(u)=a(u)+r,\qquad P_0(u)=p(u)+r,\qquad D_0(u)=d(u)-r,\qquad h=2r/b.
$$
The standard trim removes $2\varepsilon$ at each end in the $e$ coordinate. For sufficiently small $\varepsilon$ the two trimmed lifts still overlap and cover $[A_0,D_0]$. By the equal-height midpoint argument in the accompanying proof their heights glue to a single convex function $f_u$ there. In particular $P_0$ has the same value on both lifts. Write $M(u)=f_u(D_0(u))$ and $\omega(u)=\sup f_u-\inf f_u$ on this interval. All these functions are measurable, for example the extrema of $f_u$ can be taken on a countable dense set after an affine rescaling.

Choose interior $x\in(a,c)$ and $z\in(p,d)$ with $(x+z)/2=a+1/2$. One explicit choice interpolates simultaneously between the pairs $(a,p)$ and $(c,d)$ until the specified average is reached. The strict width inequalities and compactness give uniform distances from all relevant interval endpoints. For small $\varepsilon$, the endpoints $x+r,z+r$ remain uniformly interior, and have a positive-lift torus midpoint at $A_0$ in the same row. Thus
$$
 2 f_u(A_0)\le f_u(x+r)+f_u(z+r).
$$
If $f_u(A_0)>f_u(D_0)$, convex interpolation makes both interior values strictly smaller than $f_u(A_0)$, a contradiction. Therefore $M$ is the maximum. The gap $g=M-f_u$ is nonnegative and concave on $[A_0,D_0]$. At the uniformly interior point $x+r$ it is at least $\gamma_I\omega(u)$ for a constant $\gamma_I>0$. Indeed connect a point of maximum gap to each interval endpoint; the two chords give this bound by the normalized distance to the nearer endpoint. The midpoint inequality now yields
$$
 M(u)-f_u(A_0)\ge \tfrac12\gamma_I\omega(u).
$$

Take as endpoints the positive point $A_0(u-h)$ and the negative point $P_0(u+h)$. The affine identity for $d$ gives their negative-lift midpoint exactly at $D_0(u)$: the mean of their $e$ values plus $1/2$ equals $d(u)-bh+r=d(u)-r$. Their ordinary primary heights average to $u$. Consequently
$$
 M(u-h)+M(u+h)-2M(u)\ge \tfrac12\gamma_I\omega(u-h).
$$
Both inequalities hold away from the finite set of removed rows and their translates, sufficient for integration.

Take a smooth nonnegative cutoff $\chi$ compactly supported in $(0,V)$ and equal to one on a fixed neighbourhood of $I$, using the estimates above on a compact buffer about its support. Integrate the last inequality against $\chi$. Moving the difference operator to the cutoff gives an integral of $M(u)[\chi(u-h)+\chi(u+h)-2\chi(u)]$. Extend $M$ outside its needed buffer by any fixed value in the range of $F$. Subtracting a constant makes its sup norm at most $R_\varepsilon$. The $L^1$ norm of the cutoff's second difference is at most $h^2\|\chi''\|_1$, by integrating its second derivative against the triangular kernel. This proves the quantitative estimate
$$
 \int_I\omega(u)\,du\le C_I\varepsilon^2 R_\varepsilon .
$$

**2. Interior weights.** At any trimmed point on either lift in a row of $I$ whose $e$ lies in $[A_0,D_0]$, the intersection of its lift with $[A_0,D_0]$ has length bounded below uniformly on $I$. Choose a second endpoint in that interval with angular $e$-separation between two fixed positive constants below $1/2$; the same-lift ordinary midpoint also belongs. The squared circular separation in the theorem is the ordinary squared $e$-separation. All three energies are within the range $\omega(u)$, whence $w_\varepsilon(X)^2\le C_I\omega(u)$. Integrating over both lifts and using part 1 gives an $O_I(1)$ integral of $w_\varepsilon^2$ when $R_\varepsilon=O(\varepsilon^{-2})$. In particular the integral of $\log^+ w_\varepsilon$ on this part is $O_I(1)$. Its physical area tends to the area of the exceptional polygon over $I$.

**3. Remainder.** On any nonempty trimmed physical angular arc of length $L\le1$, any endpoint can be joined within the arc to a second one with physical separation $L/8$ toward the longer side. Their ordinary midpoint remains in the arc. The doubled circular separation is $L/4$. Hence $w_\varepsilon(X)\le4\sqrt{2R_\varepsilon}/L$, also outside the exceptional band. Under the range assumption this implies
$$
 \log^+ w_\varepsilon(X)\le \log(1/\varepsilon)+C+\log(1/L).
$$
The integral of $\log(1/L)$ is bounded uniformly on the entire polygon: each arc contributes $L\log(1/L)\le1/e$ in its row and the number of arcs per primary coordinate is at most two. Thus the remaining integral divided by $\log(1/\varepsilon)$ is at most the area of the remainder plus $o(1)$. First take $\varepsilon$ to zero and then exhaust $(0,V)$ by compact intervals $I$. Using $|T_\varepsilon|\to A$ proves the theorem.

**Sharpness in the stated class.** In #173780 the bounded height of range $O(K)$ has angular weight bounded below by $c\sqrt{1+K\,\operatorname{dist}(s,[1/2,1/2+V])^2}$ with $K$ a fixed multiple of $\varepsilon^{-2}$. Take that smaller weight itself. Its normalized positive logarithm tends pointwise to one outside the closed exceptional band and to zero inside. A uniform bound and dominated convergence, using the trimmed indicators, give the integral limit $1-B/A$. The earlier weighted construction and its lower bound are due to eilamc14. The present result identifies an optimality property of its block metric.
