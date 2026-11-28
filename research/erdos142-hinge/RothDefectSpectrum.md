# Distribution of midpoint defects and their Fourier contribution

Put $D(x,y,z)=x+z-2y$. Let $s=s(n)$ be any eventually nondecreasing function tending to infinity with $s=o(\sqrt{\log n})$. There is a set of lengths of logarithmic density one, depending only on this function, with the following property. For every sequence of three-term-progression-free $A\subseteq[n]=\{0,\dots,n-1\}$ on those lengths satisfying $M=|A|=(1-o(1))r_3(n)$, the conclusions below hold. All errors are uniform in the displayed parameters for a given extremality error. A set of logarithmic density one omits lengths with total reciprocal weight $o(\log X)$ up to $X$.

For every $1\le q\le e^s$, residue $b\bmod q$, real $|u|\le1$ and $ne^{-s}\le H\le n$, set $h=H/n$. Then
$$
\#\{(x,y,z)\in A^3: |D(x,y,z)-nu|\le H,\ D(x,y,z)\equiv b\bmod q\}
=(1+o(1))\frac{M^3}{q}\int_{u-h}^{u+h}\rho(v)\,dv, \tag{1}
$$
where $\rho(v)=1/2-v^2/4$ for $|v|\le1$, $(2-|v|)^2/4$ for $1\le|v|\le2$, and zero elsewhere. At $u=0$ the integral is $h-h^3/6$. This counts ordered triples with repetitions allowed, as in the exact odd-displacement identity of [the packing note](RothDefectPacking.md). At defect zero alone there are exactly $M$ triples. In particular the odd positive displacements $t\le H$ produce, on average, $(1+o(1))(M^3/n)(1-h^2/6)$ ordered nonconstant progressions in $2A\cup(2A+t)$.

There is a complementary statement about the *exact* progression count. Write $F(\theta)=\sum_{x\in A}\exp(2\pi i x\theta)$ on $\mathbb R/\mathbb Z$. For $W=e^s$, let $\mathfrak M(q,W)$ be the union of arcs of radius $W/n$ about $a/q$ for $0\le a<q$. For each $q\le e^s$, uniformly,
$$
\int_{\mathfrak M(q,W)} F(\theta)^2\overline{F(2\theta)}\,d\theta
=(1/2+o(1))M^3/n. \tag{2}
$$
The complementary integral equals $-(1/2+o(1))M^3/n$. Consequently, outside these arcs some frequency satisfies $|F(\theta)|\ge(1/2-o(1))M^2/n$. One can simultaneously exclude the arcs about *all* rationals with denominators at most $\lfloor s/4\rfloor$ by choosing their least common multiple for $q$. For arbitrary individual $q$ the witnessing frequency may depend on $q$.

## Capacity on a grid of intervals and residue classes

Write $R(n)=r_3(n)$, $j=\lfloor\log_2 n\rfloor$ and $G(i)=\log(2^i/R(2^i))$. Subadditivity makes $G$ nondecreasing, and the Behrend lower bound gives $G(i)\ll\sqrt{i+1}$. Let $\ell_j=\lceil20(s(2^{j+1})+\log(j+2))\rceil$. Eventually $\ell_j<j/2$. The variation $v_j=G(j+\ell_j)-G(j-\ell_j)$ tends to zero outside a density-zero set of indices. In fact on $K\le j<2K$ the sum of the $v_j$ is at most $(2\ell_{2K}+1)G(3K)=o(K)$, by counting the multiplicities of the nonnegative first differences. On each dyadic block of indices discard those above the square root of the block average (if the average is zero, discard none). These discarded blocks of lengths $2^j\le n<2^{j+1}$ have logarithmic density zero. For example $s=(\log n)^{1/3}$ gives $v_j\le j^{-1/12}$ after discarding indices with cardinality $O(K^{11/12})$ per block, by Markov's inequality. [Behrend-type lower bound](https://arxiv.org/abs/2406.12290)

Partition $[n]$ into $J=\lceil e^{4s}\rceil$ contiguous intervals of lengths differing by at most one, and intersect each with the residue classes modulo $q$. Each resulting cell is an arithmetic progression of $\ell=n/(qJ)+O(1)$ points. For $a=2^{j-\ell_j}$, $B_0=2^{j+\ell_j}$, the capacity of a cell is at most $\lceil\ell/a\rceil R(a)$ and $R(B_0)\le\lceil B_0/n\rceil R(n)$. Hence, on the retained lengths, every cell has capacity per site at most
$$
\frac{R(n)}n\, e^{v_j}(1+a/\ell)(1+n/B_0)=(1+o(1))M/n.
$$
Here $a/\ell$ and $n/B_0$ tend uniformly to zero by the choice of $\ell_j$. This argument gives a **pointwise upper bound** for every grid-cell average and permits some cells to be empty.

Let $B(x)$ be the average of $1_A$ in the cell containing $x$, and put $U(x)=\alpha=M/n$ on $[n]$. Both functions are zero outside $[n]$. For some $\eta=o(1)$ we have $0\le B\le(1+\eta)\alpha$ and $\sum B=M$. Thus $\sum|B-U|\le2\eta M$ and $\sum(B-U)^2\le\eta M^2/n$. The second bound follows by summing $B^2\le(1+\eta)\alpha B$.

## Counting in a narrow window

Choose a uniform point from $A$, then replace it by a uniform point of its cell. The replacement has point probabilities $B(x)/M$, changes position by at most $w=\lceil n/J\rceil$, and preserves the residue. Three independent replacements change the defect by at most $4w$. Consequently the count in (1) is between the $B$-weighted counts for radii $H-4w$ and $H+4w$.

For either radius $T$, change the three factors $B$ to $U$ one at a time. Once the coordinate of the changed factor is fixed, another endpoint always remains free (one of $x,z$). For each choice of the third coordinate there are at most $1+2T/q$ choices for that endpoint. The change in the weighted count from all three replacements is therefore at most $6\eta M n(1+\eta)^2\alpha^2(1+2T/q)$. This is $O(\eta M^3 H/(qn))$ uniformly, since $q/H=o(1)$.

For uniform integer points the probability of the congruence and window is $1/q$ times the probability of the window plus $O(1/n)$: for fixed $y,z$ the possible $x$ form an interval in which one residue has count within one of its average. Coupling the three integer points with the floors of $n$ times independent uniform variables on $[0,1]$ changes the normalized defect by at most $4/n$. The continuous density is $\rho$ as displayed: convolve the triangular density of the sum of two independent uniform variables with the uniform density on $[-2,0]$. It is bounded, and its integral over the stated window is $\gg h$ uniformly for $|u|\le1$, $0<h\le1$. The relative errors from the two radius changes and lattice rounding are $O(w/H+q/H)=o(1)$. This proves (1), including for even $q$.

## Isolating the signed Fourier contribution

Write $\widehat B,\widehat U$ with the same normalization as $F$. For $|\beta|\le 2W/n$ let $E_r(\beta)$ be the sum of $(1_A-B)(x)\exp(2\pi i\beta x)$ in residue $r\bmod q$. In each cell the unweighted sum of $1_A-B$ is zero. Subtract the exponential at its first site throughout that cell. The variation is at most $2\pi|\beta|w$, and the total absolute mass of $1_A-B$ in a residue is at most twice its $B$-mass, which is $O(M/q)$. Hence $|E_r(\beta)|\ll|\beta|wM/q$. Orthogonality on $\mathbb Z/q$ gives
$$
\sum_{a=0}^{q-1}|F(a/q+\beta)-\widehat B(a/q+\beta)|^2
=q\sum_{r=0}^{q-1}|E_r(\beta)|^2\ll M^2\beta^2 w^2.
$$
Integrating and using Parseval on $B-U$ yields
$$
\int_{\mathfrak M(q,2W)}|F-\widehat U|^2
\ll (M^2/n)(\eta+W^3/J^2)=o(M^2/n).
$$
The arcs are disjoint for large $n$. Doubling $\theta$ maps $\mathfrak M(q,W)$ into $\mathfrak M(q,2W)$ and preserves Lebesgue measure on the full circle, so the same bound holds for the doubled argument on the smaller arcs.

On the smaller arcs, both $F$ and $\widehat U$ have $L^2$ norm $O(M/\sqrt n)$ since $\|\widehat U\|_2=M/\sqrt n$. Each has supremum at most $M$. Expand the difference between $F^2\overline{F(2\theta)}$ and $\widehat U^2\overline{\widehat U(2\theta)}$ by changing one factor at a time. Cauchy–Schwarz with the preceding bounds makes its integral $o(M^3/n)$. For the uniform function, the integral on the whole circle is $\alpha^3\lceil n^2/2\rceil$, by counting ordered endpoints of equal parity. Outside the arc around zero, the geometric-series bound $|\widehat U(\theta)|\ll (M/n)/\|\theta\|$ gives squared integral $O(M^2/(nW))$, where $\|\theta\|$ is distance to an integer. This proves (2). Orthogonality makes the integral for $F$ on the whole circle exactly $M$, negligible compared with $M^3/n$ by the Behrend lower bound. Finally $\int |F(\theta) F(2\theta)|\,d\theta\le M$ by Parseval, giving the claimed frequency.

For the simultaneous denominator assertion, $\log\operatorname{lcm}(1,\ldots,m)\le 4m\log2$ for $m\ge1$. For a dyadic endpoint $2b$, the lcm up to $2b$ divides the lcm up to $b$ times $\binom{2b}{b}$: a prime power newly crossed in $(b,2b]$ contributes at least one to the binomial's prime valuation and each prime crosses at most one new power. Iterate over powers of two and round $m$ up. Thus the required common modulus is at most $e^s$.

The exact progression identity and the large-coefficient step are classical ingredients of Roth's Fourier argument. Here the restriction to near-maximal sets at typical lengths permits the growing system of arcs and the evaluation of its signed contribution. No formula for $r_3(n)$ follows from these estimates. [Green, Fourier analysis and Roth's theorem](https://people.maths.ox.ac.uk/greenbj/papers/additive-combinatorics.pdf)
