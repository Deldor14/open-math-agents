# The critical length for random subsets avoiding arithmetic progressions

Fix $k\ge3$. Write $R(n)=r_k(n)$ and $U(n)=n/R(n)$. For $0<p\le1$ let $S_p(n)$ be the independent $p$-random subset of $[1,n]$ and $\alpha_k(S)$ the largest size of a subset of $S$ avoiding nonconstant $k$-term progressions. Define
$$
 Z_n(p)=\sum_{I\subseteq[1,n],\,I\ {\rm free}}p^{|I|},
 \qquad B=\lceil p^{-(k-1)}\rceil.
$$
There are constants depending only on $k$ such that
$$
 \sup_{n\ge1}\frac{\mathbb E\alpha_k(S_p(n))}{p R(n)}
 \ \asymp_k\
 \sup_{n\ge1}\frac{\log Z_n(p)}{p R(n)}
 \ \asymp_k\ U(B).                                                \tag{1}
$$
Both lower comparisons already hold at $n=B$. In particular, up to a constant independent of $p$ and $n$, the largest relative gain from random thinning is the reciprocal extremal density at a **single explicit length**. This determines the loss in the comparison uniformly over ambient lengths. It does not assert that all ambient lengths achieve the supremum.

Here is the uniform estimate and its tail version:
$$
 \log Z_n(p)\le C_k\,p R(n)U(B),\qquad
 \Pr\{\alpha_k(S_p(n))\ge h\}\le 2^{-h}\exp(C_k\,pR(n)U(B)).     \tag{2}
$$
The same upper tail holds for the set of distinct outputs of independent labels whenever the expected number of labels landing at any given site is at most $p$. No lower bound on $pR(n)$ is needed in the finite estimates.

For context, Balogh, Liu and Sharifzadeh derived sparse bounds from deterministic upper bounds on $r_k$, and Morris, Ortega and Rué bounded the unweighted count at every length. The proof below uses their affine restriction and container methods. The estimate retains the true value $B/R(B)$ across the full range of $p$. [Balogh–Liu–Sharifzadeh](https://arxiv.org/abs/1605.03172), [Morris–Ortega–Rué](https://arxiv.org/html/2607.17746v1).

## A bound for each refinement

Two estimates from the [all-length sampling proof](RothAllLengthSampling.md) will be used, with the scale in its affine estimate kept explicit. Take $M=R(n)$ and $\beta=1/\lceil\log_2 k\rceil$. Apart from the bounded cases $n<4$, an induced container $C$ admitting a cover of weight at most $q|C|$ with edges of size $2,\ldots,k$ satisfies
$$
 |C|\le32M U(b)\quad\text{for some integer }1\le b\le 4q^{1-k}.
                                                                    \tag{3}
$$
Indeed in that proof $b=\lfloor n/(2\ell)\rfloor$, where $\ell$ is the sampled progression length. Constants throughout can be enlarged for $n<4$.

If $b\le BD$ with $B,D\ge1$ integers, then
$$
 U(b)\le C_k U(B)\exp(C_k[\log(2D)]^\beta).                       \tag{4}
$$
For $b\le B$, splitting $[B]$ into $b$-blocks gives $U(b)\le2U(B)$; for $B\le b\le2B$ use monotonicity of $R$. For larger $b$, put $a=\lfloor b/(2B)\rfloor$, so that $R(b)\ge R(B)R(a)$ by the guarded-digit product, and $b/(Ba)\le4$. Apply the [Rankin–O'Bryant lower bound](https://arxiv.org/abs/0811.3057) at $a\le D$.

Fix $c_k>0$ small enough for [Campos–Samotij, Theorem A](https://arxiv.org/html/2408.06617v2) and use $q_i=c_k p\,2^{-4i}$ for integers $i\ge0$. By (3)–(4), the children from a refinement at $q_i$ have size at most
$$
            A_k M U(B)\,2^i.                                      \tag{5}
$$
In fact the ratio $b/B$ is at most $4c_k^{1-k}2^{4(k-1)i}$. The extra factor in (4) grows as $\exp(O_k((1+i)^\beta))$, bounded by $A_k2^i$ because $\beta<1$. Choose $A_k$ once for all stages.

## Weighting the fingerprints

Put $T=pM U(B)$ and $W_i=A_kM U(B)2^i$. Descend through the successive size caps $W_{i+1},W_i$ until $W_0$. Start above the root size $n$, or stop immediately if $n\le W_0$. At a parent $V$ having $|V|\le W_{i+1}$, refine with $q_i$. Every admissible set $I\subseteq V$ has a fingerprint $F\subseteq I$ and lies in a child $C_F$ as in (5). Remove $F$ from the next ground set. The remainder $I\setminus F$ is still free, and its weight times $p^{|F|}$ equals the initial weight. Thus iterating adds each selected fingerprint site once. A node already within the next cap can be retained with empty fingerprint.

Each fingerprint has size at most
$$
 J_i=8k^2 q_i W_{i+1}\ll_k T\,2^{-3i}.
$$
For $H_i=2^{2i+2}$, the weights of all possible fingerprints at that node sum to at most
$$
 \sum_{F\ {\rm possible}}p^{|F|}
 \le H_i^{J_i}(1+p/H_i)^{|V|}.
$$
This follows termwise from $H_i^{|F|}\le H_i^{J_i}$ and the binomial identity on the full powerset. Its logarithm is at most
$$
 J_i\log H_i +pW_{i+1}/H_i
 \ll_k T\big((i+1)2^{-3i}+2^{-i}\big).
$$
At a terminal node the full powerset has weight at most $\exp(pW_0)$. Multiplying the stage bounds and adding their logarithms gives $\log Z_n(p)\le C_kT$. The use of $F\subseteq I$, and the removal of $F$ before the next refinement, are necessary for this weighted count.

## Sharpness and independent labels

For Bernoulli retention, the expected number of free subsets of $S_p(n)$ is $Z_n(p)$ exactly. The realization contains at least $2^{\alpha_k(S_p(n))}$ such sets. Jensen's and Markov's inequalities give both the expectation and the tail estimates. For independent labels each finite set $J$ is present with probability at most $p^{|J|}$. Indeed one can sum over injections of the sites into labels that produce them. The sum is at most the product of the individual site loads when the injectivity requirement is dropped. This gives the same upper estimates.

Take $n=B$ and thin with probability $q=p/4$. One can make the resulting set free by deleting at most one point for each progression. There are at most $B^2$ progressions, so
$$
 \mathbb E\alpha_k(S_p(B))\ge Bq-B^2q^k\ge pB/5.
$$
Here $Bp^{k-1}\le2$ and $k\ge3$. Monotonicity under a coupling justifies using the smaller $q$. Jensen gives $\log Z_B(p)\ge(\log2)\mathbb E\alpha_k(S_p(B))$. Dividing by $pR(B)$ proves the lower bounds in (1).

The [displacement experiment](RothExtremalSamples.md) gives one application. Use independent uniform choices in $a+\{0,t,\ldots,(d-1)t\}$ for each site in a free $A\subseteq[1,n]$, with $(d-1)t\le n$. The maximum site load is at most $\delta=R(d)/d$. The upper tail in (2) holds with an exponent $O_k(\delta R(n)U(\lceil\delta^{-(k-1)}\rceil))$ since the ambient interval has at most $2n$ sites. The smaller-scale extremal density here is the actual density of progression-free sets.

## Arbitrary finite sets of integers

In (2) one may replace the interval by **any nonempty finite host** $H\subset\mathbb Z$, put $M=\alpha_k(H)$ and use $Z_H(p)=\sum_{I\subseteq H,\ I\ {\rm free}}p^{|I|}$. The factor $U(B)$ still uses the interval extremal function. Consequently the suprema in (1) can equally well range over all finite hosts. We prove the required replacement for (3) explicitly. Affine coloring of arbitrary sets has classical antecedents in the [work of Komlós, Sulyok and Szemerédi and Ruzsa's treatment](https://matwbn.icm.edu.pl/ksiazki/aa/aa72/aa7248.pdf). Here a cover of the progressions lets one discard only specifically identified pairs of sites.

Let $C\subseteq H$ admit a cover $\mathcal G$ as in (3). Set $b=\lceil q^{1-k}\rceil$ and choose a prime $P>\max(16b,\max H-\min H)$. Take $L=\lfloor P/(8b)\rfloor$ and a free $T\subseteq\{0,\ldots,b-1\}$ of size $R(b)$. Select bins
$$
 J_i=\{4Li,\ldots,4Li+L-1\}\subset[0,P/2),\qquad i\in T.
$$
Map the input by $x\mapsto ux+v\bmod P$ for independent uniform $u,v\in\mathbb F_P$, allowing $u=0$. Distinct input sites have independent uniform images, since their residues differ and two affine evaluations determine the coefficients. Retain the sites of $C$ landing in selected bins. If all sites of a progression survive this step, their images satisfy the modular second-difference equation and have representatives in $[0,P/2)$. The integer second differences therefore vanish. Writing each representative as $4Li+e$ with $0\le e<L$, the error second difference has absolute value less than $2L$. It follows that the bin indices also have zero second differences. As $T$ is free, the whole progression must land in **one** bin. This reasoning also covers constant image progressions when $u=0$.

Designate two different sites of each cover edge. Whenever their images lie in the same selected bin, remove the first site if present. This hits every remaining progression because it contains an edge of the cover. The expected size after these deletions is at least
$$
 |C|R(b)L/P-|\mathcal G|R(b)(L/P)^2
 \ \ge\ \tfrac78 |C|R(b)L/P
 \ \ge\ \tfrac7{128}|C|/U(b).
$$
Indeed $|\mathcal G|\le q^{1-k}|C|$, $L/P\le1/(8b)$ and $L/P\ge1/(16b)$. All surviving sets are free subsets of $H$, so $|C|\le(128/7)M U(b)$. This substitutes directly for (3), at every node of the same weighted recursion. The bound is independent of the diameter of $H$.

Taking $p=1$ shows that the total number of free subsets of any finite integer host is at most $\exp(C_k\alpha_k(H))$. For arbitrary hosts the constant in this logarithmic bound is at least $\log(2^k-1)/(k-1)$. To see this, use disjoint translates of $\{0,\ldots,k-1\}$ with high digits $3^j$ and digit base $2k$. A progression forces zero second differences separately in the two digits. As the powers of three avoid even three-term progressions, each forbidden progression is exactly one full block. With $m$ blocks there are $(2^k-1)^m$ free subsets and the maximum size is $(k-1)m$.

A consequence concerns composition of random thinnings. Put $D_k(p)=\sup_H\mathbb E\alpha_k(H_p)/(p\alpha_k(H))$ over nonempty finite integer hosts. Condition first on independent retention with probability $p$, then thin the resulting host with probability $q$ (the empty host contributes zero). This gives $D_k(pq)\le D_k(p)D_k(q)$. Conversely retaining the previously selected maximum with probability $q$ gives $D_k(pq)\ge D_k(p)$. Hence $x\mapsto D_k(x^{-1/(k-1)})$ is nondecreasing and submultiplicative on $[1,\infty)$ and agrees within fixed factors with $\lceil x\rceil/R(\lceil x\rceil)$ everywhere. This comparison uses the weighted bound for arbitrary intermediate hosts.

## A sharp bound for fixed-size sets

Write $I_s(n)$ for the number of free $s$-subsets. For any integer $b\ge1$ and $1\le s\le M$ such that $M/s\le b^{1/(k-1)}/U(b)$,
$$
 \frac{s\, I_s(n)^{1/s}}{M}\le C_k U(b).                          \tag{6}
$$
Choose $p=s/(M U(b))$. Then $B=\lceil p^{-(k-1)}\rceil\le b$, whence $U(B)\le2U(b)$ by the interval partition. Since $I_s(n)p^s\le Z_n(p)$, (2) gives (6).

To see the precision of this bound, put $\gamma=(k-2)/(k-1)$ and let
$$
 E(x)=\sup_{\substack{n\ge1,\ 1\le s\le R(n)\\R(n)/s\le x}}
                    sI_s(n)^{1/s}/R(n).
$$
Then for all sufficiently large $b$,
$$
          E(R(b)/b^\gamma)\asymp_k b/R(b).                        \tag{7}
$$
The witnesses to the lower bound can have $s\to\infty$ and $s/R(n)\to0$. Here is an explicit choice. Fix a small constant $a_k>0$. For $s=\lfloor a_k n^\gamma\rfloor$ and large $n$, the expected number of progressions in a uniformly random $2s$-subset is at most $n^2(2s/n)^k\le s/2$, choosing $2^k a_k^{k-1}\le1/2$. At least half of all $2s$-subsets thus contain a free $s$-subset. Double counting gives $I_s(n)\ge\binom ns/(2\binom{2s}s)$ and $s I_s(n)^{1/s}\ge n/8$.

Fix an integer $t$ with $2(4t)^\gamma<a_k R(t)$, possible since $R(t)=t^{1-o(1)}$. Set $n=\lfloor b/(2t)\rfloor$. For all sufficiently large $b$ we have $n\ge b/(4t)$, $s\ge a_k n^\gamma/2$, and $R(b)\ge R(t)R(n)$. These give $R(n)/s\le R(b)/b^\gamma$, as (7) requires. The lower bound for $sI_s(n)^{1/s}$ and $R(n)\le R(b)$ finish the comparison. Thus (6) has the right scale, even with ranks growing as a power of the ambient length.

## Checks and remaining question

[Six Lean lemmas](RothCriticalSampling.lean) verify the powerset weight, exact removal of the compulsory fingerprint, the tilted fingerprint sum, extraction of one rank, projection onto bin indices, and uniqueness of a field-affine map for arbitrary ordered evaluations. [The exact enumerations](check_roth_critical_sampling.py) test the generating function against the Bernoulli model and compare it with an independently optimized free size. They also check 82,668 affine maps on noninterval hosts and the finite thinning composition comparison. The iteration, critical comparison and asymptotic deductions have written proofs. Formula (1) still involves extremal sizes at the variable ambient lengths in the supremum. Evaluating those independently to obtain an explicit equivalent for $R(n)$ remains open.
