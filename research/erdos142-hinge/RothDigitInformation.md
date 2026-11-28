# Digit information and the density exponent in the three-term Erdős problem

Fix a natural integer $d\ge2$. Let $R(n)$ be the maximum size of a subset of the integers $[0,n)$ containing no nonconstant three-term arithmetic progression. Use natural logarithms. Write $D_t=\log(2^t/R(2^t))$. For a nonempty progression-free $A\subset[0,2^d)$ put $D_A=\log(2^d/|A|)$. With $X$ uniform on $A$, define
$$I_j(A)=I(X\bmod 2^j;\lfloor X/2^j\rfloor),\qquad 1\le j<d.$$
Here $I(U;V)=H(U)+H(V)-H(U,V)$ is mutual information in nats. It is zero precisely when the two blocks of digits are independent.

## A characterization of the unknown exponent

Let $\beta=\liminf_{t\to\infty}\log D_t/\log t$. For fixed $0<\eta\le1$, define $J_\eta(d)$ as follows. Among the $d-1$ information values for $A$, take the $\lceil\eta(d-1)\rceil$-th smallest. Minimize this value over all nonempty progression-free $A\subset[0,2^d)$ with $D_A\le10\sqrt d$. Then
$$\boxed{\displaystyle
\liminf_{d\to\infty}\frac{\log(1+J_\eta(d))}{\log d}
=\frac{\beta}{2(1-\beta)}.} \tag{1}$$

The test class uses an explicit size threshold. It contains every maximizer, by the lower bound $R(n)\ge n\exp(-4\sqrt{\log n})$. For $2^t\le n<2^{t+1}$, monotonicity and $R(2^{t+1})\le 2R(2^t)$ bound the difference between $\log(n/R(n))$ and $D_t$ by $\log2$. Thus $\beta$ is also the liminf exponent of the density deficit on general intervals, using $\log\log n$ as denominator. The currently available bounds give $1/6\le\beta\le1/2$. At those two endpoints the right side of (1) is $1/10$ and $1/2$, respectively. Equation (1) transfers bounds on exponents in either direction. Its proof leaves the value of $\beta$ open. [Behrend bound in mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Additive/AP/Three/Behrend.html) · [Raghavan, Theorem 1.1](https://arxiv.org/abs/2603.27045v3)

## Finite inequality and extraction

Choose any $k$ interior cuts $0=j_0<j_1<\cdots<j_k<j_{k+1}=d$. Put $\ell_i=j_i-j_{i-1}$ and write $Y_i$ for the corresponding consecutive blocks, from low to high. Then
$$\sum_{r=1}^k I_{j_r}(A)\ \ge\ \sum_{i=1}^{k+1}D_{\ell_i}-D_A.\tag{2}$$
Indeed, fixing the blocks outside $i$ leaves a set of allowed values for $Y_i$ which is progression-free in $[0,2^{\ell_i})$. The map back to $X$ is an integer translation and a positive dilation. Hence $H(Y_i\mid Y_{-i})\le\log R(2^{\ell_i})$. By the entropy chain rule
$$H(X)-\sum_i H(Y_i\mid Y_{-i})
=\sum_i I(Y_i;Y_{>i}\mid Y_{<i})
\le\sum_{i=1}^{k}I(Y_{\le i};Y_{>i}).$$
The final term on the right sums the cut informations. Substituting $H(X)=\log |A|$ proves (2). The same proof bounds the sum of the actual nonnegative costs $c_i=\ell_i\log2-H(Y_i\mid Y_{-i})$ by $D_A+\sum_r I_{j_r}$.

Suppose $b$ positions have $I_j\le h$. Choose their most frequent residue modulo a positive integer $t$ and retain its $k\ge b/t$ positions. Successive retained cuts are at least $t$ apart. Partition into dyadic intervals to get $D_s\ge D_t$ for $s\ge t$. It follows for $h<D_t$ that
$$b\le t\frac{D_A+D_t}{D_t-h}.\tag{3}$$
There is a concrete extraction when $k\ge2$. Some interior block of length $s\ge t$ has $c_i\le C=(D_A+kh)/(k-1)$. Some choice of the outside coordinates leaves a progression-free fiber of size at least $2^s e^{-C}$, since its logarithmic size is at least the average conditional entropy. Partition this fiber's digit interval into $2^{s-t}$ intervals and translate the densest back to zero. This produces a progression-free subset of $[0,2^t)$ with at least $2^t e^{-C}$ elements.

For example, for every fixed $0<\gamma<1/10$, uniformly for all $A$ in our test class, all but $o(d)$ cuts satisfy $I_j>d^\gamma$. Apply (3) with $t=\lfloor d^\nu\rfloor$, $6\gamma<\nu<3/5$ and $D_t\gg t^{1/6}/\log(2t)$. Then $d^\gamma=o(D_t)$ and $t\sqrt d/D_t=o(d)$. This quantitative corollary uses the cited progression bound.

## Proof of (1)

Suppose $J_\eta(d)\le d^\gamma$ along arbitrarily large $d$, for some $0<\gamma<1/2$. Choose a minimizing $A$, take $t=\lfloor d^{1/2+\gamma}\rfloor$, and perform the extraction with $h=d^\gamma$. Here $k\ge\eta(d-1)/t\to\infty$, so $C=O_\eta(d^\gamma)$ and $D_t\le C$. Taking a liminf yields $\beta\le\gamma/(1/2+\gamma)$. As $\beta\le1/2$, this gives the lower bound in (1), including the endpoint $\beta=1/2$.

In the reverse direction, take $t\to\infty$ on a sequence attaining $\beta$, an optimal seed $U\subset[0,2^t)$, $g=D_t+\log2$, and
$$k=\max(1,\lfloor t/g^2\rfloor),\qquad d=k(t+1).$$
Use all $k$-digit integers in radix $2^{t+1}$ whose digits lie in $U$. If $x+z=2y$, reduction modulo the radix gives equality in the lowest seed digit, because both digit sums are in $[0,2^{t+1}-2]$. The seed is free so the three digits are equal. Divide off the digit and repeat. The resulting set has $|U|^k$ points and deficit $kg$. If $k\ge2$ then $kg\le\sqrt{kt}$; when $k=1$ the Behrend bound gives $g\le5\sqrt t$. Both satisfy the prescribed threshold.

Distinct seed digits of a uniform point are independent. At a cut between seed digits the information is zero. Within a seed, the independent full digits on the two sides leave only the mutual information between the two pieces of that seed. Its upper bound is $t\log2-\log|U|=D_t$, since the top bit in each radix digit is fixed. Thus every cut has $I_j\le D_t$. Finally $g\le5\sqrt t$ gives $k\asymp t/g^2$ with absolute constants, even when the maximum defining $k$ is one. Since $\log g/\log t\to\beta$, one has $\log d/\log t\to2(1-\beta)$. This proves the upper bound in (1) for every indicated quantile, including the maximum.

## A finite theorem for sampled blocks and matrix rank

At cut $j$, write $x=u+2^jv$ and let $K_j$ be the least number of actual columns $v$ whose occupied rows together cover all occupied $u$. The following bound holds for every selection of cuts:
$$|A|\le\prod_{i=1}^{k+1} R(2^{\ell_i})\prod_{r=1}^k K_{j_r}.\tag{4}$$
For the first cut, each chosen column has at most $R(2^{\ell_1})$ rows, so the union has at most $K_{j_1}R(2^{\ell_1})$ rows. Fix any such row. After deleting its fixed low digits, the suffix is progression-free. The representative columns at every higher cut still cover its rows, by retaining precisely the residues with those fixed low digits. Induction proves (4), also for arbitrary integer radices. A column basis of any matrix over any field with precisely this support meets every occupied row. It follows that (4) still holds when each $K_j$ is replaced by such a matrix rank, even with different fields or nonzero weights at different cuts. Formula (3) and its almost-all-cuts corollary also hold for $\log K_j$ by the same selection argument.

For the real zero-one support matrix, a separate bound is $e^{I_j}\le\sum_{(u,v)\in A}1/(r_uc_v)\le\mathrm{rank}_{\mathbb R}$, where $r_u,c_v$ are the row and column occupancies. Jensen's inequality gives the first bound by averaging $\log(|A|/(r_uc_v))$ over the points. The sum in the middle is the squared Frobenius norm after normalizing rows and columns by the square roots of their occupancies and deleting empty indices. The normalized matrix has operator norm at most one by Cauchy–Schwarz applied over its occupied entries. Summing the squares of its singular values gives the final bound.

## Verification

The arbitrary-radix product bound for representative columns, the rectangle-cover version, the separated-cuts consequence, and the matrix-rank comparison have Lean proofs. Lean also verifies the entropy inequality (2) for every finite set in the theorem and every list of positive integer radices. The definition in the source is mutual information multiplied by the cardinality, expressed directly through the multiplicities of the low and high digits. The subadditivity lemma uses the real inequality $\log z\le z-1$ and sums over all occupied pairs. The passage to asymptotic exponents in (1) is a written proof for review. An exact-arithmetic verifier enumerates all 4,150 nonempty three-term-free subsets of $[0,16)$ and all eight choices of cuts for each, checking (2) and (4) as integer inequalities. The same program checks the normalized-matrix inequality and the binary-field rank bound. It independently checks 2,412 cut information values across 360 guarded products. [Information inequality](RothFiniteInformation.lean) · [Sampled columns](RothSampleColumns.lean) · [Rectangular covers](RothDigitCuts.lean) · [Separated cuts](RothSeparatedCuts.lean) · [Matrix rank](RothDigitRank.lean) · [Finite verifier](check_roth_digit_scales.py)
