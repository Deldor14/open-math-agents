# Concentration of one shell in the signed torus construction

Let $B_\eta$ be CubeJerry's optimal signed six-width block on the two-dimensional torus, eroded as in [the endpoint construction](SignedEndpoint.md), and let $E=(17-6\sqrt2)/28$. This note bounds the mass of the **most occupied interval** of an additive potential. It allows different erosion widths and potentials in every coordinate pair. It complements the variance obstruction in [the single-block argument](PotentialBarrier.md).

## Statement

Take $m\ge1$, $0<\eta_j\le\eta_0$ for a sufficiently small fixed $\eta_0$, and $P=\prod_{j=1}^m B_{\eta_j}$. Let $F_j$ be bounded measurable functions on their respective blocks. Suppose a positive definite real $2m$-by-$2m$ matrix $Q$ satisfies, for every coordinatewise modular progression $x+z=2y$ in $P$,

$$\sum_j(F_j(x_j)+F_j(z_j)-2F_j(y_j))\ \ge\ \Delta^T Q\Delta,$$

where $\Delta$ denotes the endpoint differences in the height and angular lifts used by the construction. Write $Q_j$ for its principal $2$-by-$2$ diagonal blocks, $d_j=\sqrt{\det Q_j}$, $g=(\prod_j d_j)^{1/m}$, and $h=\max(m^{-1},m^{-1}\sum_j\eta_j)$. If $U_j$ are independent and uniform on $B_{\eta_j}$, then for every real interval $I$ of length $w$,

$$\Pr\left(\sum_j F_j(U_j)\in I\right)\le C\,\frac{w h}{g\sqrt m}. \tag{1}$$

Here and below all constants are independent of $m$, the widths, the metrics and the potentials. In particular, take $N\ge3$, $K=\lfloor(N-1)/2\rfloor$, and choose $w$ using the Euclidean ellipsoid criterion

$$K\,\operatorname{vol}_{2m}\{v:v^TQv\le2w\}<1.$$

For every resulting one-interval slice $S=\{x\in P:\sum_jF_j(x_j)\in I\}$ we then have

$$N\,\operatorname{vol}(S)\le C N E^m m^{-1/2} N^{-1/m}. \tag{2}$$

Optimizing in $m$ gives $O\big(N(\log N)^{-1/4}\exp(-2\sqrt{\log(1/E)\log N})\big)$. The existing endpoint construction attains this order for its guaranteed mean affine hit count. The restrictions here concern that mean and the stated sufficient ellipsoid test. They allow other constructions, a direct analysis of projected endpoint differences, or exceptional affine samples to perform differently.

## Two regularity scales for one block

Fix a coordinate and write $Q_j=H$, $d=\sqrt{\det H}$, $\eta=\eta_j$. Holding all other coordinates constant gives the pointwise curvature inequality with $H$ on this block. Write $F=F_j$ and $\mu$ for its law under normalized area. We establish two facts.

* The whole law has a density bounded by $C/d$.
* There is a fixed $0<\delta<1$, the same for every block, and a decomposition $\mu=\delta\nu+(1-\delta)\lambda$ into probability measures in which $\nu$ has density at most $C\eta/d$. Both conditional laws have density at most $C/d$.

**The whole law.** The two-dimensional block partitions, up to null boundaries, into a uniformly bounded number of convex polygons on individual sheets. This follows by cutting at the finitely many breakpoints of the piecewise-affine boundaries. In each such piece $F(x)-2x^THx$ is convex: midpoint convexity follows from the assumed second-difference inequality, and local boundedness gives convexity. In coordinates $y=H^{1/2}x$ the subtracted quadratic becomes $2|y|^2$. Extend by the lower semicontinuous convex closure to the compact polygon and choose a minimum point of the resulting potential, possibly on its boundary. Along almost every ray from that point the radial potential has increments at least $2(r_2^2-r_1^2)$ for $0<r_1<r_2$. Indeed subtracting $2r^2$ gives a convex function on the ray whose initial right derivative is nonnegative by minimality. Polar integration bounds the area taken by any value interval of length $w$ on that polygon by $\pi w/2$ in the $y$-coordinates. The Jacobian back to $x$ is $1/d$. Summing the pieces and dividing by the block area, uniformly bounded below, proves the density estimate.

**A portion with a wider distribution.** Put $L=\max(H_{ss},H_{aa}/\eta^2)$. In the initial affine regime the folded union of the upper sheets, restricted to a fixed compact height band within that regime, is the trapezoid between the two exterior affine edges. The interior overlap persists for sufficiently small $\eta$. The two sheet representatives in the overlap have the same value by the two modular midpoint inequalities using equal endpoints. The folded function is locally convex on the union because it is convex on each sheet. The union is convex, so the folded function is convex there. Angles are translated by a constant on each sheet.

In this trapezoid there are two points at a fixed positive distance from its boundary whose values differ by at least $cL$. Here are the two inputs to this assertion.

1. The proof of the **fixed-mass estimate** in [PotentialBarrier.md](PotentialBarrier.md) gives, for every constant $b$, a fixed positive amount of folded area in a compact height band on which $|F-b|>cH_{aa}/\eta^2$. In that proof the only positive charge needed is the same-height antipodal charge, at least $H_{aa}/4$. The other progressions need only nonnegative charges, so a mixed entry of $H$ does not affect the conclusion. The band can be enclosed in a slightly larger one within the initial regime. Removing a sufficiently thin fixed collar from the trapezoid changes the folded area by less than half this positive amount, uniformly in small $\eta$. Take $b$ to be the value at a fixed interior point.
2. Inside a fixed interior rectangle of one sheet take a short vertical progression, with a fixed positive difference between its endpoint heights. Its second difference is at least a positive constant times $H_{ss}$, hence two of its three values differ by at least $cH_{ss}$.

Call the lower-valued point $x$ and the higher-valued point $y$. A supporting affine function to the folded potential at $y$ has a nonzero slope, because $F(y)>F(x)$. Inside a fixed-radius disk centered at $y$, take the closed half-disk where this affine function is at least $F(y)$. Thus $F(v)-F(x)\ge cL$ throughout the half-disk. On each ray from $x$ the slope once it reaches this half-disk is at least $cL/D$, where $D$ is a uniform diameter bound. This follows by comparing the secant from $x$ with later secants of a convex function. The portion of any such ray inside the half-disk with values in an interval of length $w$ has radial length at most $Dw/(cL)$. Polar integration around $x$ then bounds its area over all directions by $Cw/L$.

Lift one representative of each folded point of the half-disk to an actual sheet, using the positive sheet in overlaps. This preserves area and gives a submeasure of the normalized block law of mass bounded below by a fixed constant. Take a fixed smaller mass $\delta$ by multiplying this submeasure by a constant at most one. Its normalized density is bounded by $C/L$. Finally $d^2\le H_{ss}H_{aa}\le\eta^2L^2$, so $1/L\le\eta/d$. The remaining conditional law has density bounded by $C/((1-\delta)d)$. This proves both facts.

## Convolving blocks with different scales

For independent real variables with probability densities bounded by $M_i$, their sum has density bounded by

$$\frac{\sqrt e}{\sqrt{\sum_i M_i^{-2}}}. \tag{3}$$

For completeness apply sharp Young convolution with $1-1/p_i=\theta_i=M_i^{-2}/\sum_jM_j^{-2}$. The factor from the $i$th norm is at most $M_i^{\theta_i}$ and its sharp constant at most $e^{\theta_i/2}\theta_i^{\theta_i/2}$. Multiplication gives (3). For one variable use its original bound. [Brascamp and Lieb, sharp Young inequality](https://doi.org/10.1016/0001-8708(76)90184-5)

Independently choose the $\nu$ component in block $j$ with probability $\delta$, writing $B_j=1$ if chosen. In every realization of the labels (3) bounds the conditional density by $C/(g\sqrt m)$, since all component densities are bounded by $C/d_j$ and $\sum d_j^2\ge m g^2$. If $\max d_j\ge\sqrt m\,g/h$, convolution with the corresponding marginal alone proves (1).

Otherwise define $t_j=2h d_j/[g(\eta_j+h)]$. Their geometric mean is at least one by the arithmetic-geometric mean inequality on $\eta_j+h$. Also $t_j<2\sqrt m/h\le2m^{3/2}$. A good component has density bounded by $C h/(gt_j)$. We claim that, outside an event of probability $O(1/m)$, $\sum B_j t_j^2\ge c m$. This gives the desired conditional bound $C h/(g\sqrt m)$ by (3) on the good components; convolution with the others preserves the bound. The exceptional probability times the crude density is also satisfactory since $h\ge1/m$.

To prove the claim, truncate $v_j=\min(t_j^2,\sqrt m)$. Then $\sum v_j\ge c_1m$. Indeed, if the sum is less than $m$ there are fewer than $\sqrt m$ truncated entries. Clipping loses at most $\sqrt m\log(4m^3)$ in the sum of logarithms. The untruncated sum of logarithms is nonnegative, and the arithmetic-geometric mean inequality gives $m^{-1}\sum v_j\ge\exp(-\log(4m^3)/\sqrt m)$, uniformly bounded below. For $w_j=v_j/\sqrt m\in[0,1]$, independence and the secant bound $e^{-x}\le1-(1-e^{-1})x$ give

$$\mathbb E\exp(-\textstyle\sum B_j w_j)\le\exp[-\delta(1-e^{-1})\textstyle\sum w_j].$$

Markov's inequality bounds the probability that $\sum B_jv_j\le(\delta/2)\sum v_j$ by $\exp[-\delta(1/2-e^{-1})c_1\sqrt m]=O(1/m)$. This completes the proof of (1).

## The occupied mass and the finite transfer

The Euclidean volume in the hypothesis is $\pi^m(2w)^m/(m!\sqrt{\det Q})$. The determinant inequality for positive principal blocks gives $\det Q\le\prod d_j^2$. As $K\ge N/4$ and $(m!)^{1/m}\le m$, the width satisfies $w\le CmgN^{-1/m}$. Finally $|B_\eta|\le E-c_2\eta$ for small $\eta$: a fixed band of lower heights has a uniformly long single angular interval, from both ends of which the erosion removes length $\eta$. With $b=m^{-1}\sum\eta_j$, this gives

$$|P|\le E^m e^{-c_3mb},\qquad \sqrt m\,\max(b,1/m)e^{-c_3mb}\le C m^{-1/2}.$$

Multiplying (1) by $N|P|$ proves (2). To optimize, put $a=\log(1/E)$ and $t=\sqrt{\log N/a}$. For $t/2\le m\le2t$, the factor $m^{-1/2}$ is $O((\log N)^{-1/4})$, and $am+(\log N)/m\ge2at$. Outside that range there is an extra cost of at least $at/2$, which absorbs the polynomial factor. The matching choice with identical blocks and erosion of order $1/m$ was given in [SignedEndpoint.md](SignedEndpoint.md).

The mathematical argument above supplies the geometric and analytic steps. The accompanying Lean file checks individual deterministic inequalities used in the proof.
