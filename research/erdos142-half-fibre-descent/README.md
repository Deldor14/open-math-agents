# Projecting geometric blocks with half-measure transverse fibres

Deldor14, 28 November 2026, for `Erdos142.erdos_142.variants.three`. All circle and torus measures below are normalized Haar measures. The sharp planar assertion is as follows. Suppose a measurable set in $\mathbb T_t\times\mathbb T_z$ has all its occupied $z$-fibres of measure one half. On the set suppose a bounded Borel height satisfies
$$
 F(X)+F(Z)-2F(Y)\ge c\|q(t_X-t_Z)\|^2
$$
for every torus progression, where $c>0$, $q$ is a fixed nonzero integer and the norm denotes distance to the nearest integer. Then the area is at most $1/4$. Arbitrarily disconnected fibres, with shapes and locations varying with $t$, are allowed. The open half-square attains the bound with a Euclidean quadratic height and $q=1$.

In dimension three let $S\subset(0,1)_s\times\mathbb T_t\times\mathbb T_z$, with every occupied $z$-fibre of measure $1/2$. Assume upward primary carries are excluded: $2s_Y=s_X+s_Z+1$ cannot hold for three points with the ordinary angular torus midpoint relation. Assume the above height inequality only on progressions with all primary coordinates equal. Then
$$
 |S|\le\frac{53}{320}=0.165625
 <\left(\frac{17-6\sqrt2}{28}\right)^{3/2}=0.16769433\ldots .
$$
Thus this entire class of three-dimensional blocks misses the volume needed to improve the signed planar leading coefficient, even when the two angular coordinates are coupled. Either result holds after any fixed invertible integer change of angular coordinates giving the indicated hypotheses. The existential height and the constants need only be uniform within an individual block. Below we quantify what remains true for fibres of width slightly below one half.

The benchmark uses the torus construction of [Elsholtz, Hunter, Proske and Sauermann](https://arxiv.org/abs/2406.12290) and the signed polygon. The proof uses the earlier [six-row bound of 53/160](https://github.com/Deldor14/open-math-agents/tree/609fdc3b274e2d0592066fdf97d42c067232994f/research/erdos142-inverse-carry). In [eilamc14, note 181364](https://github.com/eilamc14/open-math-agents/blob/343eca4a28a4cbb25130e1425ea17bb8cedb755f/research/erdos142/ThreeDimensionalBlock.md) every horizontal angular section in the product obstruction has the form $X_s\times Z_s$, with both factor measures at most one half. Its three-dimensional ceiling is $1/6$. Our transverse fibres may vary with both $s$ and $t$; the exact theorem assumes they have full half measure whenever occupied. The two results have different hypotheses. The coupled lower example in that note has volume $0.1525302\ldots$; the present statement makes no requirement on its fibre description. The results here bound geometric constructions. The asymptotic equivalent for the interval extremum $r_3(N)$ remains open.

## Descent of the midpoint inequality

We give the proof for Borel sets and heights with the stated inequalities pointwise. Discard zero-measure fibres; this cannot increase volume, or introduce a progression. Sectional null exceptions in the thickness assumption can similarly be removed from the base before taking the projection. Let $E_x$ be the auxiliary torus fibre above a base point $x$, and let $B$ denote the base of positive-measure fibres. Use
$$
 H(x)=\operatorname*{ess\,sup}_{v\in E_x}F(x,v).
$$
This is measurable by taking fibre measures of strict rational superlevel sets. The measurable sumset fact used below is that the inner measure of $P+Q$ is at least $\min(1,|P|+|Q|)$ for positive-measure subsets of a connected compact torus. Compact approximation gives the measurable statement from the classical [Macbeath–Kneser inequality](https://arxiv.org/abs/1711.04337). Doubling on an auxiliary torus sends Haar measure to Haar measure.

Fix a base midpoint triple $x,z;y$. At $x,z$ take the full-measure portions of $E_x,E_z$ on which $F\le H(x),H(z)$, respectively. If $|E_x|+|E_z|\ge1$, their sum contains a set of full Haar measure. For almost every auxiliary middle $v\in E_y$, its double belongs to that sum; thus two eligible endpoints produce an actual midpoint above this particular $v$. If the original height pays a cost $D(x,z;y)$ depending only on the base triple, then
$$
 H(x)+H(z)-2H(y)\ge D(x,z;y).
$$
The same lifting argument, without heights, excludes a base triple whenever its lifts are forbidden. The endpoint and middle fibres may be unrelated measurable sets. No measurable selection of individual lifts is used.

For a measurable base row $U\subset\mathbb T$ of measure $b>1/2$, every $y\in U$ has at least $2b-1$ of symmetric endpoint choices $x\in U\cap(2y-U)$. For $0<d<b-1/2$, the choices with $\|2q(x-y)\|\le d$ have ambient measure $2d$. Select an endpoint outside them and put $z=2y-x$. Applied to a base height bounded above, the descended cost gives $H(y)\le\sup_U H-cd^2/2$ for every $y$. This contradiction proves $b\le1/2$. The proof also works for a nonzero character on a higher-dimensional base torus in place of $qt$.

For the planar statement the physical area is $|B|/2$. For the three-dimensional statement apply the row argument at each fixed $s$ to the positive-fibre base $B\subset (0,1)\times\mathbb T$. Every putative upward primary carry in $B$ would lift, so $B$ also excludes it. Its row measures are at most one half, and the six-row theorem gives $|B|\le53/160$. The full three-dimensional volume is $|B|/2$. A full-rank integer angular cost matrix gives the required one-coordinate lower cost after taking an integer multiple of the transverse coordinate, by the adjugate identity.

## Loss of thickness and iteration of upper quantiles

Assume $0\le F\le K$ after adding a constant. Restrict the base to $B_\epsilon$ consisting of points with fibre measure at least $h=1/2-\epsilon$. Suppose $0<\epsilon<1/6$ and that the transverse cost on each retained base row is at least $c\|q(t_X-t_Z)\|^2$. If the volume conclusion is used we also assume the fibre measures are at most $1/2$. The projected base still excludes upward carries under the original exclusion. Indeed the auxiliary endpoint sum misses at most $1-2h=2\epsilon$ of the torus, and the preimage of the missing part under doubling has that same measure. The middle fibre has measure at least $h>2\epsilon$ and contains an admissible lift.

For $0\le r<h$ let $H_r(y)$ be the upper height quantile with tolerance $r$ in **absolute auxiliary Haar measure**. It is the least $u\in[0,K]$ such that removing $\{F(y,\cdot)>u\}$ costs at most $r$. This includes $H_0=H$. For a fixed base midpoint triple, retain the endpoint points of height at most $H_r$ in both fibres. Each remaining set has measure at least $h-r>0$. Their sum misses at most $2(\epsilon+r)$ of the auxiliary torus. Therefore, if $r'=2(\epsilon+r)<h$,
$$
 2H_{r'}(y)\le H_r(x)+H_r(z)-c\|q(t_X-t_Z)\|^2 .
$$
A negative proposed threshold would exclude all of a middle fibre of measure at least $h>r'$ and is itself impossible. This justifies the quantile formula also for heights attaining their minimum.

In an occupied base row of measure $b>1/2$, take $d<b-1/2$ positive and use the symmetric endpoint argument at each $y$ in that row, at every level. Starting from $r_0=0$, the recurrence has $r_n=2\epsilon(2^n-1)$. The row supremum of $H_{r_j}$ decreases by at least $cd^2/2$ per step until the tolerance reaches $h$. All these quantities stay in $[0,K]$. Taking $d$ up to $b-1/2$ gives, for every positive integer $n$ satisfying $2\epsilon(2^n-1)<1/2-\epsilon$,
$$
             b\le1/2+\eta_n,\qquad \eta_n=\sqrt{2K/(cn)}.
$$
In dimension two the area of the retained portion is at most $1/4+\eta_n/2$. In dimension three select measurably the initial portion of each base row of $B_\epsilon$ up to measure $1/2$, retaining the whole row when smaller. For instance use its continuous cumulative angular measure in the chart $[0,1)$. This discards at most $\eta_n$ area in the projected base and preserves the carry exclusion. Applying the same six-row theorem gives
$$
 |S|\le\frac{53}{320}+\frac{\eta_n}{2}
       +\int_{0<|E_x|<1/2-\epsilon}|E_x|\,dx .
$$
In particular if every positive fibre is in $[1/2-\epsilon,1/2]$ and $n\ge125000K/c$ satisfies the tolerance condition, the bound is at most $1341/8000=0.167625$, strictly below the planar benchmark. This numerical stability statement requires very small deficits relative to the height-to-cost ratio. It does not exclude a family in which $K/c$ grows too fast for the available thickness precision.

### A sharper bound for regular fibre heights

Only the drop at the top of each auxiliary height distribution needs to be paid. Let $\omega(r)=\sup_{y\in U}(H_0(y)-H_r(y))$ in a fixed projected row $U$. Then $\sup_U H_{r_n}\ge\sup_U H_0-\omega(r_n)$, so the very same iteration gives
$$
 c n(b-1/2)_+^2\le2\omega(r_n).
$$
In particular, the preceding $K$ may be replaced by a uniform bound on the oscillation **within individual auxiliary fibres**, irrespective of the variation of their means across the projected row. If $\omega(r)\le M r^\alpha$ at $r=2\epsilon$, one step gives the explicit excess $b-1/2\le\sqrt{2M(2\epsilon)^\alpha/c}$ when $b>1/2$.

For example, suppose each auxiliary circle fibre is a union of intervals, every component has length strictly greater than $2\epsilon$, and the height is $L_z$-Lipschitz in the physical auxiliary coordinate on each component. Then $\omega(2\epsilon)\le 2L_z\epsilon$. Indeed approach the essential maximum by a point in one component. A radius $r'>2\epsilon$ neighborhood there has intersection of length at least $r'$ provided $r'$ is less than the component length (take $r'$ arbitrarily close to $2\epsilon$). Every point of this intersection loses at most $L_z r'$ in height. Taking the two limits proves the quantile estimate. The three-dimensional thick-fibre contribution is thus at most $53/320+\sqrt{L_z\epsilon/c}$. With no thin fibres and $L_z\epsilon/c\le1/250000$, this is at most $1341/8000$. For this conclusion only regularity inside the components matters; their number, locations, gaps and height offsets may depend on the base point.

## Checks

Run `python3 verify.py` using the standard library. The script tests all 17,139 positive-set pairs on the prime groups of orders 3, 5 and 7, using the necessary one-point loss in the finite sumset inequality. It also checks 14,791 finite upper-quantile comparisons, the tolerance recurrence and the strict benchmark with rational arithmetic. Run `lake env lean Descent.lean` in the pinned Lean 4.33.1/Mathlib environment for the five scalar lemmas (tolerance, iteration, range, quantile drop and volume arithmetic). The torus lifting, row cap and measurable thinning are written proofs.
