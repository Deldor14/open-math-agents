# Universal transfer along a curved profile

Let $R(n)=r_3(n)$ and $[N]=\{0,\ldots,N-1\}$. Given a real function $\Phi$ on $[0,1]$ and $E\ge0$, define $K_\Phi(N,E)$ to be the largest number of sites $S\subseteq[N]$ admitting integer labels $f(y)$ with
$$ |f(y)-N\Phi(y/N)|\le E\quad(y\in S), $$
such that for every three-term-progression-free input $A\subseteq\mathbb Z$, the selected sites $\{y\in S:f(y)\in A\}$ are also free. The labels, sites and intercepts within the permitted tube may vary arbitrarily with $N$.

Suppose $\Phi$ is twice continuously differentiable with $\Phi'\ge c>0$ and $\kappa\le\Phi''\le K$ for fixed $\kappa>0$. Uniformly along $2\le E=o(N)$, put $m=\lceil\sqrt{N/E}\rceil$. Then
$$
 \boxed{\displaystyle K_\Phi(N,E)\asymp_{\Phi}\sqrt{NE}\,R(m).} \tag{1}
$$
The same conclusion holds for $-K\le\Phi''\le-\kappa$. In particular a bounded-error rule for $\Phi(x)=x+x^2$ can use order $\sqrt N R(\lceil\sqrt N\rceil)$ sites. Its density tends to zero. A straight line of the same positive range of slopes admits bounded-error rules of positive density, as quantified in [the rounding theorem](RothRounding.md). Formula (1) relates the curved capacity to the ordinary finite Roth number; its constants and the asymptotic for $R$ are separate questions.

## The upper bound from long steps

Set $g(y)=N\Phi(y/N)$ and choose
$$
 D=\left\lceil\max\{3E/c,\ 3\sqrt{NE/\kappa}\}\right\rceil.
$$
On an output progression $y-d,y,y+d$ with $d\ge D$, successive labels increase by at least $cd-2E>0$. Each second difference of $g$ has magnitude at least $\kappa d^2/N$: integrate $g''$ against the triangular kernel $d-|u|$ on $[-d,d]$. Replacing the values by the integer labels changes the second difference by at most $4E$. Thus the three labels are distinct, in increasing order, and have nonzero second difference. They form a free input, which would select an output progression. Such a triple cannot occur.

Each residue class modulo $D$ therefore selects an ordinary progression-free set after division by the step. This gives the finite upper bound
$$ K_\Phi(N,E)\le D\,R(\lceil N/D\rceil). \tag{2} $$
For the asymptotic range in (1), $D\asymp_\Phi\sqrt{NE}$ and $\lceil N/D\rceil\asymp_\Phi m$.

## Matching lower bound by local linear rules

Choose $L=\lfloor\sqrt{NE/\max(1,K)}\rfloor$ and $M=\lfloor N/(2L)\rfloor$, for $N$ large in the stated range. Take a largest free set $U$ in $[M]$. For each $u\in U$ allow sites from the block $2Lu+[L]$. If three sites in these blocks form a progression, the second difference of their offsets has magnitude strictly less than $2L$. It must be divisible by $2L$, so both offsets and block indices form progressions. The three block indices are equal by the choice of $U$. This argument is independent of the label choices in different blocks.

In a chosen block approximate $g$ by its tangent line $\ell(y)$ at the first site. Taylor's estimate gives $|g(y)-\ell(y)|\le KL^2/(2N)\le E/2$. Let $v=\min(1/2,c)>0$. For a shift $b\in[0,1)$ keep the sites with $\{\ell(y)+b\}\in[0,v)$ and label them $\lfloor\ell(y)+b\rfloor$. Averaging $b$ gives at least $vL$ sites for some choice in each block. The integer labels differ from the tangent line by less than one, so they stay in the prescribed tube. On an output progression in the block their second difference is zero: it is an integer and the fractional parts vary over a half-open interval of width at most $1/2$. A label fiber fits in a half-open interval of length $v/\ell'\le1$ and has at most one site. Every output progression therefore requires an input progression. The union is a universal rule, giving
$$ K_\Phi(N,E)\ge vL\,R(M). \tag{3} $$
Here $L\asymp_\Phi\sqrt{NE}$ and $M\asymp_\Phi m$. Monotonicity and the block partition $R(b)\le\lceil b/a\rceil R(a)$ for positive integers $a,b$ compare $R$ at arguments within fixed factors, proving (1).

For a general $C^2$ increasing profile with derivative bounded below, every weak limit of $N^{-1}\sum_{y\in S}\delta_{y/N}$ for universal rules with $E=o(N)$ is supported on the zero set of $\Phi''$. Indeed (2) holds locally on every interval with curvature bounded away from zero, with the number of sites per residue class reduced proportionally to the interval length. Its normalized occupancy tends to zero by $R(k)/k\to0$. The open set where the curvature is nonzero has a countable cover by such intervals. The normalized counting measures are dominated in the limit by Lebesgue measure, so endpoints cause no exception. [Roth density bound, in a quantitative form](https://arxiv.org/abs/2309.02353)

The [Lean file](RothRounding.lean) checks the integer half-phase construction used for rational slopes and the signed-error calculation that excludes a progression when the underlying second difference is too large. Taylor's theorem, the block construction and the full comparison (1) are given here as a written proof.

## All nonaffine real-analytic profiles

Formula (1) also holds for **every nonaffine real-analytic $\Phi$ on a neighborhood of $[0,1]$**, including every polynomial of degree at least two. It allows stationary points and changes of curvature. In particular for $\Phi(x)=x^2$ the same $\sqrt{NE}\,R(m)$ order holds even at the stationary endpoint.

Write $\delta_R(v)=R(v)/v$ for positive integers. We first need the following uniform comparison, valid for every $\epsilon>0$:
$$ \delta_R(a)\le C_\epsilon (m/a)^\epsilon\delta_R(m)\qquad(1\le a\le m). \tag{4} $$
For $m/a<4$ this follows by monotonicity. Otherwise put $b=\lfloor m/(2a)\rfloor$. The sets $x+2ay$ from independent optimal sets in $[a]$ and $[b]$ give $R(m)\ge R(a)R(b)$ by the same digit argument as above. Since $b\ge m/(4a)$, the Behrend bound $R(b)\gg_\epsilon b^{1-\epsilon}$ proves (4) for $0<\epsilon<1$ and hence for larger $\epsilon$. [Behrend-type constructions](https://arxiv.org/abs/2406.12290)

The zeros of $\Phi'\Phi''$ on $[0,1]$ form a finite set and have finite orders. On its complement away from small neighborhoods of those points, (2) works with fixed constants and with either sign of the first or second derivative. Near a zero, split each side into dyadic intervals where the distance from it lies between $w/2$ and $w$. Finite order gives fixed $A\ge1$ and $c_0>0$ with $|\Phi'|\ge c_0 w^A$ and $|\Phi''|\ge c_0 w^{2A}$ on each such interval. Both signs are fixed on the interval, and $A$ can be chosen uniformly over all zeros.

For this interval choose $D_w=\lceil C_\Phi\sqrt{NE}\,w^{-A}\rceil$. Strict order and a nonzero second difference follow as in (2) for steps at least $D_w$, since $E\le\sqrt{NE}$. Write $u=m w^{A+1}$. Whenever $u$ exceeds a sufficiently large constant, the interval contains $B\asymp Nw$ consecutive integer sites and $\lceil B/D_w\rceil\asymp u$. The residue-class bound is at most $C_\Phi Nw\,\delta_R(\lfloor u\rfloor)$, using monotonicity and subadditivity for fixed-factor changes of argument. By (4) this is
$$ O_{\Phi,\epsilon}\big(N\delta_R(m)\,w^{1-(A+1)\epsilon}\big). $$
Choose $\epsilon=1/(2(A+1))$ and sum the convergent geometric series. The remaining central interval near each zero has at most $O_\Phi(Nm^{-1/(A+1)}+1)$ sites, also $O_\Phi(N\delta_R(m))$ by (4) with $a=1$. This proves the upper bound.

For the lower bound choose one fixed positive-length subinterval with $|\Phi'|$ bounded below; negate the labels and profile if needed. Use (3) on whole blocks inside that subinterval with the global bound on $|\Phi''|$. The available index interval has length a fixed positive multiple of $m$, and subadditivity gives a corresponding constant multiple of $R(m)$. This proves the extension.
