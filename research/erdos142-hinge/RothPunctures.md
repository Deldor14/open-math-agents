# How many deletions change the finite Roth number?

Write $R(n)=r_3(n)$ for the largest size of a subset of $[n]=\{1,\ldots,n\}$ avoiding nonconstant three-term arithmetic progressions, and $R(0)=0$. A **blocker** is a set meeting every such subset of size $R(n)$. Let $b(n)$ be the smallest blocker size. For a finite set $S$ let $\alpha(S)$ be its largest progression-free cardinality.

There are two different density statements. For a set of lengths $n$ of **natural density one**, forbidding any of a growing number of sites leaves the optimum *exactly* unchanged. On dyadic shells of **logarithmic density one** we can instead compute, to first order, the worst loss when a positive or slowly vanishing fraction of sites is forbidden. The latter result gives matching lower and upper bounds. Both use the actual $R(n)$.

## Exact survival and exceptions

Let $s(n)$ be the least length with $R(s(n))=R(n)$ and put $u=n-s(n)+1$. Write $\chi_3(w)$ for the fewest colors in a coloring of $[w]$ with no monochromatic three-term progression. Then
$$
 \lceil u/R(u)\rceil\le \chi_3(u)\le b(n)\le u. \tag{1}
$$

Indeed take an optimal $A\subseteq[s(n)]$. All $u$ translates $A+t$, $0\le t<u$, are optimal inside $[n]$. Any blocker $T$ supplies a color to each offset by choosing a site in $(A+t)\cap T$. The offsets assigned to one site $x$ lie in $x-A$, a progression-free set. This proves the lower bounds. Removing the final $u$ sites leaves $[s(n)-1]$ and reduces the optimum. More generally, each fixed site hits at most $R(w)$ of the $w$ translates of an optimal subset of $[n-w+1]$. Thus for $1\le w\le n$ and $|T|=t$,
$$
 \alpha([n]\setminus T)\ge R(n-w+1)-\lfloor tR(w)/w\rfloor .
$$

The function $R$ has increments zero or one. There are exactly $R(X)$ nonempty constant stretches up to $X$. Only the first $w-1$ lengths of each stretch can have $b(n)<\chi_3(w)$. Hence
$$
 \#\{n\le X:b(n)<\chi_3(w)\}\le (w-1)R(X). \tag{2}
$$
In particular
$$
 R(X)\le \#\{n\le X:b(n)=1\}\le 2R(X).
$$
The lower bound counts all jumps, where forbidding the last site suffices. The upper uses $\chi_3(3)=2$. More generally for every fixed $t\ge1$, the number of lengths $n\le X$ where at most $t$ forbidden sites can reduce the optimum has order $R(X)$, with a constant depending on $t$. For the upper bound use any $w$ with $w/R(w)>t$, which exists by Roth's theorem.

There is an absolute $c>0$ such that, on a set of lengths of natural density one, **any** set of at most
$$
 \left\lfloor\exp\!\left(c\frac{(\log n)^{1/36}}{(\log\log n)^{7/6}}\right)\right\rfloor
$$
sites can be forbidden while retaining all $R(n)$ points. To see this, put $F(y)=y^{1/6}/\log y$ for sufficiently large $y$. The upper bound of [Raghavan, v3](https://arxiv.org/abs/2603.27045v3) gives $R(X)/X\le e^{-aF(\log X)}$. Use $w=\lfloor e^{a F(\log X)/2}\rfloor$ in (2). The exceptional proportion tends to zero, bounded by $e^{-aF(\log X)/2}$. For all remaining lengths up to $X$, (1)–(2) give $b(n)\ge\chi_3(w)\ge w/R(w)\ge e^{aF(\log w)}$. Here $F(\log w)\gg(\log X)^{1/36}/(\log\log X)^{7/6}$. Decreasing $c$ and using eventual monotonicity replaces $X$ by $n$ and makes the admissible number strictly smaller than $b(n)$. The same argument using only the [Bloom–Sisask exponent](https://arxiv.org/abs/2309.02353) gives $\exp(c(\log n)^{1/81})$.

A singleton blocker can occur even one step after a jump. At $n=33$ there are four optimal sets of size 13. Their intersection is $\{2,32\}$, although $R(32)=13$. At $n=37$ the four optimal sets of size 14 have intersection $\{2,36\}$, and $R(36)=14$. These are the only nonjump singleton-blocker lengths through 61. The C++ search computes the Roth numbers successively and tests site avoidance at the first step after each jump. At later positions in the stretch, three translates suffice by (1). An independent Python checker enumerates AP-free halves and tests all compatible unions at the six surrounding lengths. The [published computations of finite Roth numbers](https://doi.org/10.37236/2061) concern the underlying interval capacities. Here the extra calculation determines mandatory sites. Run `c++ -O2 -std=c++17 mandatory_sites.cpp -o mandatory_sites && ./mandatory_sites 61` and `python3 check_puncture_examples.py` to reproduce the finite checks. For lines marked `next`, bit $i$ of the last column represents site $i+1$. The accompanying Lean file proves that the offsets hitting one prescribed site are progression-free and that a simultaneous avoiding translate exists if $tR(w)<w$.

## The cost of forbidding a macroscopic set

Put $H(n,m)=\min_{S\subseteq[n],\,|S|=m}\alpha(S)$. For $j\ge3$ write $e_j=(\log j)^2/\sqrt j$. Outside $O(J/\log J)$ exceptional dyadic exponents in each block $J\le j<2J$ with $J$ a large power of two, the following hold simultaneously for every $2^j\le n<2^{j+1}$.

* For **all** $0\le m\le n$, one has $H(n,m)=(m/n)R(n)+O(e_jR(n))$.
* For $m\ge n/j^2$ the relative estimate $H(n,m)=(1+O(e_j))(m/n)R(n)$ holds.
* Consequently the worst loss when forbidding $t$ sites is $(1+o(1))tR(n)/n$ whenever $t/(ne_j)\to\infty$. Removing an end interval attains that estimate to the same relative accuracy.

Here is the finite averaging step. Slide an optimal subset of $[B]$ through $[n]$ using all $B+n-1$ shifts for which the two ambient intervals can meet. Every site is covered exactly $R(B)$ times. Restricting each shift to $S$ gives
$$
 \frac{mR(B)}{B+n-1}\le H(n,m)\le R(m). \tag{3}
$$
The upper bound is realized as a *candidate* by the interval $S=[m]$. The lower also holds for arbitrary nonnegative weights, with $m$ replaced by the total weight and the conclusion about the weight captured by one progression-free subset. In particular the fractional chromatic number of the 3-AP hypergraph on $[n]$ lies between $n/R(n)$ and $(B+n-1)/R(B)$. For the upper bound give each of the restricted translates weight $1/R(B)$ in a fractional coloring.

For the choice of $B$, the function $G(i)=\log(2^i/R(2^i))$ is nondecreasing by partition into halves. The [Behrend-type lower bound](https://arxiv.org/abs/2406.12290) gives $G(i)=O(\sqrt i)$. Set $h=\lceil8\log_2(2J)\rceil$. The sum over $J\le j<2J$ of $G(j+h)-G(j-h)$ is $O(\sqrt J\log J)$ since each increment is used at most $2h$ times. Except on the stated number of exponents, that difference is at most $(\log J)^2/\sqrt J=O(e_j)$.

On a good shell let $a=2^{j-h}$, $B=2^{j+h}$ and $q=R(a)/a$. Then $R(B)/B\ge q e^{-O(e_j)}$, and $a/n,n/B=O(j^{-8})$. Partitioning any interval of length $m$ into pieces of length at most $a$ gives $R(m)\le q(m+a)$. Thus (3) places $H(n,m)$ between $(1-O(e_j))qm$ and $q(m+a)$. Taking $m=n$ shows $q=(1+O(e_j))R(n)/n$. Substitution gives both estimates, including the claim about an end interval. It also shows that the fractional chromatic number is $(1+O(e_j))n/R(n)$ on the same shells.

The exceptional shells occupy a vanishing proportion of exponents, hence a vanishing share under logarithmic weighting of the lengths. The results allow exceptions of other densities where explicitly stated. They determine how deleting sites changes the optimum in the indicated regimes. An asymptotic equivalent for $R(n)$ itself remains open.
