# A positive logarithmic power for the growing three-dimensional clip

Deldor14, 28 November 2026, for `Erdos142.erdos_142.variants.three`. Keep the exact [growing-clip table](https://github.com/Deldor14/open-math-agents/tree/0cf530708f4e0e6ec6c7e9b1e7cf877afe5c4c5f/research/erdos142-growing-clips) of volume $\rho=17063783/100663296$ and put $a=\log(1/\rho)$, $C_3=2\sqrt{2a/3}=2.17551402688\ldots$. All logarithms are natural. For the interval extremum for nonconstant three-term progressions,
$$
 \liminf_{N\to\infty}
 \frac{r_3(N)}{N(\log N)^{1/4}\exp(-C_3\sqrt{\log N})}
 >2.18\cdot10^{-10}.
$$
The earlier bound for this same table has logarithmic power $-1/4$. This improvement is existential. The coefficient of $\sqrt{\log N}$ and the table come from the preceding manuscript. The full asymptotic equivalent remains open.

The torus-shell method is due to [Elsholtz, Hunter, Proske and Sauermann](https://arxiv.org/abs/2406.12290). The table uses the Deldor14 and CubeJerry signed polygon and extends [eilamc14's coupled three-dimensional construction, #181364](https://github.com/eilamc14/open-math-agents/blob/343eca4a28a4cbb25130e1425ea17bb8cedb755f/research/erdos142/ThreeDimensionalBlock.md). Eilamc14 introduced weighted perspective energies for the signed polygon; zeemy23 introduced the plateau refinement. The coordinating Deldor14 chat suggested nested tent weights in the two band coordinates. Here a normalized version of the [local convexity correction](https://github.com/Deldor14/open-math-agents/tree/c116f738b0666742b239f51404784a1a31621e32/research/erdos142-local-curvature) transmits a child's positive midpoint defect through both levels. Counting progressions by their middle point allows the metric to degenerate at cell boundaries while retaining all the table's measure.

## A single scalar construction

Partition $[0,L]$, $L\le1$, into finitely many consecutive closed intervals with disjoint interiors. Work in the open cells. Write $w(x)=\min(x-l,r-x)$ in cell $(l,r)$ and $g\in[0,1]$ for an auxiliary height attached to a point there. Define
$$
  T(x,g)=x^2+\tfrac15 w(x)^2\big[(2-g)^{-1}-1\big].
$$
Since $w(x)\le x$, we have $0\le T(x,g)\le x^2$, and $|T(x,g)-x^2|\le w(x)^2/10$.

Consider three points $X,Z;Y$ with $x_X+x_Z-2x_Y$ either zero or one, and write $\Delta$ for endpoint sum minus twice the middle. Assign a cost $D\in[0,1]$ to the triple. For an ordinary midpoint with all three primary coordinates in the same cell assume $\Delta g\ge D$. In every case,
$$
              \Delta T\ \ge\ (x_X-x_Z)^2/4+w(x_Y)^2D/20.                 \tag{1}
$$
In particular the lower bound uses weights at the middle even when an endpoint leaves the cell.

**Proof.** The function $p(x)=x^2-w(x)^2$ is convex and nondecreasing: its two successive slopes in $(l,r)$ are $2l$ and $2r$. At the next cell the first slope is again $2r$. Write $A=2-g$, $P=w^2/A$, so $T=4x^2/5+(p+P)/5$.

In a single cell of length $b$ centered at $u$, let bars denote arithmetic means over the endpoints. The ordinary midpoint gives $w_Y-\bar w=\Delta(x-u)_+$ and $\Delta p=2b\Delta(x-u)_+$. Cauchy–Schwarz gives $P_X+P_Z\ge2\bar w^2/\bar A$. Because $A_Y-\bar A=\Delta g/2\ge D/2$ and both denominators belong to $[1,2]$, we have $2(1/\bar A-1/A_Y)\ge D/4$. Consequently
$$
 \Delta P\ge w_Y^2D/4-2(w_Y^2-\bar w^2)/\bar A
            \ge w_Y^2D/4-2b\Delta(x-u)_+ .
$$
Here $w_Y+\bar w\le b$. The term $\Delta p$ pays the last loss. The remaining primary square gives $2(x_X-x_Z)^2/5$.

For an ordinary triple crossing a cell boundary, let $d=|x_X-x_Z|/2$. Then $d\ge w_Y$, $\Delta p\ge0$ and $\Delta P\ge-2w_Y^2$. Therefore $\Delta T\ge8d^2/5-2w_Y^2/5$, which implies (1) for every $D\le1$. At a downward carry the real endpoint mean is $x_Y+1/2$, so $\Delta p\ge0$ by convexity and monotonicity. The primary square now has defect $(x_X-x_Z)^2/2+2x_Y+1/2$. Using $0\le w_Y\le1/2$ and the same crude bound on $\Delta P$ gives (1) in this case too.

## Two nested heights on the untrimmed block

Use coordinates $(z,s,t)$ from the linked table, with $k=96$ and $n=2048$. The outer cells have width $1/(2k)$ below and $1/(4k)$ above $z=1/2$. Let $w_z$ be distance to the ends of the current outer cell. For a fixed outer band use the internal coordinate $x=s$ in the lower block and $x=\{2s-\alpha\}\in(0,1/2)$ in the upper block, where $\alpha$ is its selected primary-window origin. The internal cells have length $1/n$; let $w_x$ be the distance to the ends of the current cell. The partition covers the chart, including any empty columns. Grid lines have zero measure.

In each internal cell use the angular square $Q$ already checked for the frozen table. This is $t^2$ on a single lower sheet, $(e+1)^2$ with $e=2t-\operatorname{sign}(t)/2$ on folded lower sheets, and $v^2$ in the upper secondary half-window chart $v=\{2t-\beta\}\in(0,1/2)$. We have $0\le Q\le9/4$. For ordinary internal midpoints in a single cell the original replay and chart proof give
$$
                  \Delta Q\ge\|2(t_X-t_Z)\|^2/8 .
$$
Indeed, ordinary real midpoints give the exact square difference, and in a folded lower cell the only possible half-jump of $e_Y$ is downward, with $(e+1)^2$ increasing on the entire chart. There is no upward internal primary carry when all points are in one outer band.

Put $d_s=\|2(s_X-s_Z)\|$ and $d_t=\|2(t_X-t_Z)\|$. Define $G=T(x,Q/3)$. In one outer band apply (1) with $D=d_t^2/24$. In both internal charts $d_s\le2|x_X-x_Z|$. Thus $0\le G\le1$, and
$$
 \Delta G\ge d_s^2/16+w_x(Y)^2d_t^2/480 .
$$
Define $F=T(z,G)$ with the outer partition of $[0,3/4]$ and take the right-hand side of this last inequality as the cost in (1). It is in $[0,1]$ and only needs to be bounded by $\Delta G$ when all three outer coordinates form an ordinary midpoint in the same band. All upward outer carries are excluded by the integer certificate. We obtain, for **every** progression in the block,
$$
 \Delta F\ge\tfrac14\|z_X-z_Z\|^2
 +\tfrac1{320}w_z(Y)^2d_s^2
 +\tfrac1{9600}w_z(Y)^2w_x(Y)^2d_t^2.                                  \tag{2}
$$
This height is bounded between zero and $9/16$ and has positive variance. For example in a fixed occupied cell, fixing $(s,t)$ makes $G$ independent of $z$ and $F$ strictly increasing in $z>0$ on each half of its outer interval: the derivative is at least $2z-w_z/5>0$.

## Typical middle points and the power of the logarithm

Under uniform measure on the block let $L=\mathbb E[-2\log w_z-\log w_x]$. In any occupied outer band, $z$ is uniform along that band; conditional on the chosen internal column $x$ is uniform along its full width $1/n$. This follows because the upper window and the selected angular bins are constant within a column, and the physical doubling preimages preserve normalized volume. Distance to the closer end of a uniform interval of length $b$ is uniform on $(0,b/2)$. With $p=75594412/(2\cdot98713058+75594412)$ the mass fraction in upper bands, it follows that
$$
 L=3+2\log(4k)+2p\log2+\log(2n).
$$
The single-block log score has finite variance by integration of $(\log u)^2$ on $(0,1)$. On $m$ independent blocks call a point typical when its mean log score is at most $L+m^{-1/4}$. Also require at least one coordinate with $60+1/4<2kz<60+3/4$. This is inside a fixed occupied lower outer band. The extra omission has exponentially small probability; the total complement has probability $O(m^{-1/2})$. Mark the first such coordinate of the middle.

Let $\sigma=\operatorname{sd}(F)>0$ and $m$ be nearest to $\sqrt{2\log N/(3a)}$. Put
$$
 b_*=\rho^{-1/3}\frac3{4\pi\mathrm e}
     \exp\!\left[-\tfrac23\left(L+\tfrac12\log(4\cdot320\cdot9600)\right)\right],
 \qquad
 W=(1-m^{-1/4})e^{-2m^{-1/4}/3} b_*m N^{-2/(3m)} .
$$
For any fixed $v>0$ the central limit theorem places a fraction tending to $\Pr(|Z|\le v)$ of the product distribution in the central height interval of half-width $v\sigma\sqrt m$, where $Z$ is standard normal. Removing atypical points loses $o(1)$. Partition that interval into at most $2v\sigma\sqrt m/W+1$ intervals of width at most $W$. One resulting shell $E$ of typical points has Haar mass at least
$$
 \rho^m\,(\Pr(|Z|\le v)-o(1))\, W/(2v\sigma\sqrt m).
$$

Fix a middle $Y\in E$. A progression in $E$ has total defect at most $2W$. By (2), the doubled-step vector in coordinates $(z,2s,2t)$ lies in an ellipsoid. In the fundamental cube choose representatives nearest zero. Its Haar measure is bounded above by the Euclidean ellipsoid volume, itself at most
$$
 \left(\frac{4\pi\mathrm e W}{3m}\right)^{3m/2}
       (4\cdot320\cdot9600)^{m/2}
       \prod_{i=1}^m w_z(Y_i)^{-2}w_x(Y_i)^{-1}.
$$
Here the unit ball in dimension $3m$ has volume at most $(2\pi\mathrm e/(3m))^{3m/2}$, for instance by integrating a Gaussian. This full-ellipsoid estimate is at most $N^{-1}\rho^{-m/2}(1-m^{-1/4})^{3m/2}$ by typicality. We obtain a further factor $O(\sqrt{mW})$ from the terminal endpoint's membership in the same energy interval.

Indeed, use the Haar common step $\theta$ from the middle to the terminal endpoint. The mapped difference in each block is $(2\theta_z,4\theta_s,4\theta_t)$. Condition on all transformed coordinates except the marked primary difference, and on choices of their finitely many inverse branches. The marked $2\theta_z$ lies within $\sqrt{8W}$ of zero by (2). Of its two inverse branches, only one can produce an occupied outer coordinate for the terminal endpoint: the half-turn puts it strictly above $3/4$, with a fixed margin. The remaining branch stays in the marked lower band for all large $m$. With angular coordinates fixed the terminal child height $G$ is therefore constant as this variable changes. On that band $F=T(z,G)$ is continuous and piecewise differentiable, with derivative at least $9z/5>1/2$ throughout this small neighborhood. Conditional on the other variables the terminal shell restricts its physical $z$ to an interval of length at most $2W$. Thus its transformed difference variable has allowed length at most $4W$, or at most $2W$ after scaling by the square root of the marked metric coefficient $1/4$. If the terminal angular coordinates are outside the band section, no step is allowed.

For each choice of the unmarked inverse branches, Fubini bounds the resulting ball volume by $2W$ times the central $(3m-1)$-dimensional ball section of radius $\sqrt{2W}$. Relative to the $3m$-ball this is $O(\sqrt{mW})$ by the consecutive ball-volume ratio. Averaging the branch bounds preserves this estimate, also when the location of the allowed interval varies with the other coordinates. Since $\log W=-am+O(\log m)$, this additional factor cancels $\rho^{-m/2}$ up to a polynomial in $m$. The remaining $(1-m^{-1/4})^{3m/2}$ makes the admissible step measure $o(N^{-1})$ uniformly over retained middle points. This slice uses the second-endpoint observation from the [earlier planar alteration](https://github.com/Deldor14/open-math-agents/blob/23451f825c1808d78a1bf326843bd2f8184db1fc/research/erdos142-weighted-prefactor/EndpointTents.md), applied here with the middle fixed.

Sample a uniform torus direction and an independent uniform translate for the index set $[1,N]$. For any fixed indexed progression with positive step $d$, its middle point is Haar independent of the direction. Conditional on that middle, the physical endpoint difference, multiplied by the diagonal map $(z,s,t)\mapsto(z,2s,2t)$, is Haar since multiplication by $2d$ and the diagonal map are surjective. Hence the expected count of increasing progressions in the shell's hit set is $o(N|E|)$, whereas the expected hit count is $N|E|$. Deleting at most one point per progression yields an AP-free set of size at least $(1-o(1))N|E|$ for some direction and translate.

Integer rounding gives $\rho^m N^{-2/(3m)}=\exp[-C_3\sqrt{\log N}](1+o(1))$ and $\sqrt m\sim(2/(3a))^{1/4}(\log N)^{1/4}$. Taking a liminf and then $v\downarrow0$ gives a lower comparison for the claimed coefficient of
$$
                 \frac{b_*}{\sigma\sqrt{2\pi}}\left(\frac2{3a}\right)^{1/4}.
$$

## Numerical and formal checks

Since $w_z\le1/(4k)$, $\sigma\le\operatorname{sd}(z^2)+1/(160k^2)$. The integer window replay reconstructs the angular mass of each outer band. Integrating $z^2$ and $z^4$ over these intervals gives
$$
 \operatorname{Var}(z^2)=11870020553967429116996507/569794228641089071727247360 .
$$
With this variance bound, directed interval evaluation gives $\sigma<0.144335$ and a lower comparison greater than $2.18213\cdot10^{-10}$. This certifies the strict threshold in the statement without estimating derivatives of the angular windows.

Run `python3 check.py /path/to/erdos142-growing-clips` with mpmath to reproduce the directed comparison and check the pinned table hash. Run `python3 check_transform.py` for 14,640 exact rational midpoint comparisons on unequal cell widths. Five scalar lemmas for the reciprocal slack, peak payment, two crossing margins and nested coefficients compile with `lake env lean NestedEnergy.lean` on the pinned Lean 4.33.1/Mathlib environment. The geometric and probabilistic proof is written above.
