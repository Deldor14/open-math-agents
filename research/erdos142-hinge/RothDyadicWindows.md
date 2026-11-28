# Near-uniform counts beyond the odd steps

Let $R(n)=r_3(n)$, $\alpha=R(n)/n$, and $d=\log(1/\alpha)$, with natural logarithms. Choose any power of two $1\le D\le1/\alpha$. For all sufficiently large $n$ there exist a power of two $b$ divisible by $2D$, a three-term-progression-free set $A\subset[0,n)$, and a real $\delta>0$ with
$$\begin{aligned}
\log b &\le d+\log D+4\sqrt{d+\log D}+O(\log\log n),\\
|A| &=(1+o(1))\delta n,\qquad
\log(n/|A|)\le d+4\sqrt{d+\log D}+O(1).
\end{aligned}\tag{1}$$
All bounds are uniform in $D$. Let $q$ be any positive step not divisible by $2D$, and put $g=2^{v_2(q)}$. Then $g\le D$. Every arithmetic progression in $[0,n)$ of step $q$ and $b/g$ terms contains
$$(1+O(1/\log n))\delta\, b/g\tag{2}$$
points of $A$, uniformly in the initial point and all such steps. On progressions of $s\ge b/g$ terms the relative error is $O(1/\log n+b/(gs))$. In particular all these directions obey the small relative error in (2) at length exactly $b$, by splitting into $g$ whole cycles.

For example, take $D$ to be the largest power of two at most $1/\alpha$. Among $1,\ldots,X$, at most an $\alpha$ fraction of the steps are excluded, for every $X$. The set has density at least $\alpha\exp(-4\sqrt{2d}-O(1))$ and $\log b\le2d+4\sqrt{2d}+O(\log\log n)$. Alternatively take $D$ the largest power of two at most $\exp(\sqrt d)$. Then $\log b\le d+5\sqrt d+O(\log\log n)$, while every excluded step is divisible by a power of two greater than $\exp(\sqrt d)$. The odd-step characterization in the companion is the case $D=1$. [Coprime windows](RothCoprimeWindows.md)

## Balancing the tag residues

Put $\epsilon=1/\log(2n)$ and $H=d+\log D+\log(4000\epsilon^{-2}\log(2n))$. Choose the least power of two $b\ge\exp((2+\sqrt{H+4})^2)$. Thus $\alpha b\exp(-4\sqrt{\log b})\ge4000D\epsilon^{-2}\log(2n)$. Since $D\le e^d$ and $d\le4\sqrt{\log n}$, we have $b=n^{o(1)}$ and $2D\mid b$ for large $n$. Put $w=b/2$ and choose an optimal three-term-free set $S\subset[0,w)$. Embed it in a prime field $\mathbb F_\ell$ with $b\le\ell\le2b$ and choose an invertible affine image uniformly. Crop the image back to $[0,w)$ to obtain $U$. It is free because the source has all integer second differences of magnitude less than $\ell$.

For every residue class $c\bmod D$ in $[0,w)$ the count in $U$ has expectation
$$\lambda=|S|b/(2D\ell)\ge |S|/(4D)$$
and variance at most $\lambda$, by pairwise uniformity of affine images. Behrend gives $|S|\ge(b/2)e^{-4\sqrt{\log b}}$, hence $\lambda\ge500\alpha^{-1}\epsilon^{-2}\log(2n)$. Chebyshev's inequality and a union bound over the $D$ classes give failure probability at most $D/(\epsilon^2\lambda)<1$. Fix an image with all the counts within $\epsilon\lambda$ of $\lambda$. For every $g\mid D$, every class modulo $g$ in the tags now has $(1\pm\epsilon)D\lambda/g$ elements, by summing disjoint classes. [Finite-field variance in Lean](RothAffineVariance.lean) · [Affine crop](RothAffineCrop.lean)

## Counting on reduced cycles

Take $T=\lceil n/b\rceil$, let $V$ be optimal on $[0,T)$, and set $\rho=|V|/(2T)\ge\alpha/4$. Use the independent row shifts from the companion. If $g=\gcd(b,q)\le D$, the first $b/g$ sites of any step-$q$ progression give precisely one point above every residue $u\bmod b$ with $u\equiv a\pmod g$, where $a$ is the starting site. After division by $g$, the step $q/g$ is invertible modulo $b/g$. Consequently the count is binomial with success probability $\rho$ and exactly as many trials as there are tags in that class modulo $g$. Shifts assigned to the other tags can be chosen freely. The expectation is $(1\pm\epsilon)\rho D\lambda/g$; it is at least $(1-\epsilon)\rho\lambda\ge100\epsilon^{-2}\log(2n)$ for large $n$. The usual binomial relative-error bound and the union bound over at most $n^2$ pairs $(a,q)$ supply a single assignment with (2), taking $\delta=\rho D\lambda/b$.

Now $\delta=\rho |S|/(2\ell)\ge\alpha e^{-4\sqrt{\log b}}/32$. Taking step one gives the stated cardinality by partitioning into full $b$-term windows and covering a possible remainder by the final window of $b$ terms. The same argument works at period $b/g$ for general $q$. Finally $d\gg(\log n)^{1/6}/\log\log n$ implies $\log\log n=o(\sqrt d)$. Therefore $\sqrt{\log b}=\sqrt{d+\log D}+O(1)$ uniformly over $1\le D\le e^d$. Substitution proves (1). [Raghavan, Theorem 1.1](https://arxiv.org/abs/2603.27045v3)

Lean verifies the unique representative of every admissible residue in a reduced cycle, and the exact multiplicative factor contributed by shifts on inactive rows. The original finite theorem, in which all tags are active, is formalized in the companion. The simultaneous balancing and the asymptotic estimates above are written proofs. Direct enumeration independently compares 316 progressions under two composite moduli with the binomial law on their active rows. [Reduced cycles and counts](RothRowCycles.lean) · [Enumeration](check_roth_row_cycles.py)
