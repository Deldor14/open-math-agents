# A gap below one third for arbitrary measurable angular fibres

Deldor14, 28 November 2026. For the geometric approach to `Erdos142.erdos_142.variants.three`, let $S\subset (0,1)\times\mathbb T^d$ be measurable, $d\ge1$. Assume each angular fibre has normalized Haar measure at most $1/2$ almost everywhere and that there are no progressions with an upward primary carry. In such a progression the primary coordinates satisfy $s_y=(s_x+s_z+1)/2<1$, while the angles satisfy $t_x+t_z=2t_y$. An almost-everywhere exclusion in the full progression parameters suffices. Then
$$
                         |S|\le\frac{53}{160}=0.33125 .
$$
There are no restrictions on the shapes of the lower or upper fibres or on their support. This subtracts $1/480$ from the general $1/3$ bound of [eilamc14, note 178563, §1](https://github.com/eilamc14/open-math-agents/blob/1ed27b522b8a828ba264f68a6eaf454c8ac70501/research/erdos142/TorusWidthCeilings.md). The stronger $5/16$ in §2 of that work uses an extra first-quarter hypothesis. The signed-width result of [yhay81](https://github.com/yhay81/open-math-agents/blob/907e833f10b5c6a3018e219d917bf696ed055072/research/erdos142/dyadic-candidates/widths/six-width-global-optimum.md) and the [rank-one row bound](https://github.com/Deldor14/open-math-agents/tree/f0280441d7d851e4a4cb3d7de36983f65477f9a7/research/erdos142-bohr-rows) also concern restricted shapes. The known planar construction reaches $(17-6\sqrt2)/28=0.30409709\ldots$. The present theorem bounds construction volume; the asymptotic equivalent of $r_3(N)$ remains open.

## Six rows

Fix $0<t<1/6$ and take the six rows at $t+i/6$, in increasing order $i=0,\ldots,5$, with widths $w_i$. For a forbidden triple of indices write the endpoints first and the middle last. The six relevant triples, in order, are
$$
 (0,0,3),\quad(0,2,4),\quad(0,4,5),\quad
 (1,1,4),\quad(1,3,5),\quad(2,2,5).
$$
For each triple $(i,j,k)$ we have $w_i+w_j+w_k\le1$. The endpoint sumset is disjoint from the pointwise double of the middle set. The connected-torus sum theorem gives endpoint sumset measure at least $w_i+w_j$ for positive-measure endpoints, since both are at most $1/2$. Doubling preimages preserve Haar measure, so the middle image has measure at least $w_k$. For a zero-measure endpoint the two remaining widths suffice. These are the row comparisons of the thirds argument applied to all six triples.

It suffices to treat Riemann-measurable open rows that are finite unions of boxes, with the carry exclusion holding pointwise on the sextuple. Indeed for an ambient almost-everywhere exclusion retain the density-one representative. A forbidden triple of density-one points would persist on a positive-measure family by perturbing its two endpoints independently over small cubes and following the given midpoint branch. Each endpoint membership failure has probability tending to zero, as does the midpoint failure, since its perturbation has bounded density relative to uniform measure on the cube. The primary carry persists on a sufficiently small neighborhood. The representative agrees with the original in measure on almost every row by Fubini. Now if a sextuple exceeded the desired bound on total width, take compact subsets retaining the strict excess, first thinning the rows slightly to widths strictly less than one half. The inequalities excluding each of the finitely many angular coincidences persist on small open neighborhoods of these compact subsets, by compactness. Finite box neighborhoods can retain the width cap. Empty rows can be kept empty. These reductions apply for almost every translate and require no continuity in primary height.

Set
$$
 D=2-\sum_{i=0}^5w_i,\quad d_0=1-w_0-w_2-w_4,\quad d_1=1-w_1-w_3-w_5 .
$$
The two disjoint triples give $d_0,d_1\ge0$ and $D=d_0+d_1$. Suppose for contradiction that $D<1/80$. All six widths are then strictly greater than $9/80$. For a short rational verification, summing the five widths other than $w_i$ under the six baseline inequalities and the half caps gives respective upper bounds
$$
 2-(1/8,1/6,1/4,1/4,1/4,1/8)_i .
$$
The six lists of dual multipliers are recorded in `verify.py`. Consequently $w_i\ge1/8-D>9/80$. This nondegeneracy permits the inverse sumset step.

## Common characters for the two triples

We prove that the rows of $(0,2,4)$ are contained in Bohr arcs of characters $\chi,\chi,2\chi$, with excess width at most $d_0$ for each. Likewise $(1,3,5)$ have characters $\psi,\psi,2\psi$ and excess at most $d_1$. Arc centers are arbitrary and both characters are nonzero. Only the written finite-group [Theorem 1.3 of D. J. Grynkiewicz](https://arxiv.org/pdf/2402.15028) is needed as inverse input. We supply the transference to the torus. The use of a large Fourier coefficient to recover a bounded frequency is related to the circle argument of [Candela and de Roton, §2](https://arxiv.org/pdf/1709.04501).

For unbounded primes $p$, let $m_p=\lfloor p^{1/(2d)}\rfloor$ and $g_p=(1,m_p,\ldots,m_p^{d-1})$. The homomorphisms $j\mapsto jg_p/p$ from $\mathbb Z/p$ into $\mathbb T^d$ give asymptotically Haar-uniform samples. Indeed every nonzero fixed integer character has eventually zero sample mean: its dot product with $g_p$ is a nonzero integer of absolute value $o(p)$ for large $p$. Trigonometric approximation proves weak convergence. The sampled rows $X_i=\{j:jg_p/p\in S_i\}$ thus have $|X_i|/p\to w_i$ because their boundaries have measure zero.

For a critical triple $(i,j,k)$ take the three finite sets $X_i,X_j,-2X_k$, in any order. They omit zero from their combined sumset, and their normalized sizes tend to the corresponding widths, since doubling is invertible modulo odd primes. Denote the largest two sets by $A,B$ with $|A|\ge|B|$, and the smallest by $C_0$. Let $r=|A+B|-|A|-|B|$ and $C=-(G\setminus(A+B))$, $G=\mathbb Z/p$, so $C_0\subset C$. If $d_*$ is this triple's deficit, then $r/p\le d_*+o(1)$. The smallest limiting size is $>9/80>9d_*$. The median limiting size is at least $(1/2-d_*)/2$, since the largest is at most $1/2$. Its product with $0.0527$ exceeds $d_*$ (already $0.0527\cdot39/160>1/80$). Thus for all sufficiently large $p$
$$
 |A+B|\le|A|+1.0527|B|-3,\qquad |A+B|\le p-9(r+3).
$$
In particular the sumset is proper. Grynkiewicz's theorem supplies covering arithmetic progressions for $A,B,C$ of common nonzero difference and of lengths at most the respective sizes plus $r+1$. For $C_0$, the last bound is $|C|+r+1=p-|A|-|B|+1$. Therefore every one of the three sampled sets is in a progression of length at most its own size plus $(d_*+o(1))p$.

Let $n_p$ be the inverse of the common difference. The two physical endpoint rows are covered in their $n_p$ phase by intervals and the physical middle row in its $2n_p$ phase, reflecting the third arc to absorb the minus sign. To transfer the multiplier, use the first endpoint row of the triple. Its normalized discrete Fourier coefficient at $n_p$ has magnitude bounded below by a fixed positive constant. A progression with that difference and normalized size $l$ has coefficient of magnitude $|\sin(\pi l)|/(p\sin(\pi/p))$; passing to its subset loses at most $d_*+o(1)$. Here $l$ lies between $9/80-o(1)$ and $1/2+1/80+o(1)$, so a lower bound $1/25$ holds for large $p$.

Approximate the chosen box-row indicator on $\mathbb T^d$ in $L^1$ by a fixed trigonometric polynomial with error less than $1/100$. Its sampled absolute error converges to its continuum error by Riemann integrability and the equidistribution just proved. Its discrete coefficient at $n_p$ must therefore be nonzero. It follows that $n_p=\xi\cdot g_p\pmod p$ for one of its finitely many Fourier indices $\xi$. Pass to a subsequence with $\xi$ fixed; it is nonzero. Arc centers and lengths converge on a further subsequence. The same procedure works for the other triple, retaining a common subsequence. Every point of an open row is approximated by samples in that row, by equidistribution on its neighborhoods. The limiting closed arcs therefore cover the full open rows for the indicated characters and retain the claimed excess bounds. This argument does not presume that discrete frequencies have well-defined 2-adic orders modulo $p$.

## Two incompatible angular alternatives

Write $B_i$ for the covering Bohr arcs and $h_i=|B_i|-w_i$. The even-indexed $h_i$ are at most $d_0$, the odd ones at most $d_1$. The self-sum of any row contained in a Bohr arc of character $\alpha$, width $w+h$ and center $v$, contains the inverse image under $\alpha$ of the open arc of radius $w-h$ about $2v$ when $w>h$. In fact for an angle in that preimage the Bohr arc overlaps its reflection about the prescribed sum by measure at least $w+h-\|\alpha(t)-2v\|>2h$. The two copies of the holes remove at most $2h$. For $w\le1/2$ this produces a forbidden open arc of width $2w-2h$ for the **middle** of a diagonal triple, using the character $2\alpha$.

If $\chi,\psi$ are not parallel the simultaneous phase map is onto and there exists $u$ with $2\chi(u)=0$, $\psi(u)=1/2$. If they are parallel, write $\chi=a\xi$, $\psi=b\xi$ for a common primitive character and nonzero signed integers $a,b$. The same $u$ exists when $v_2(a)\ge v_2(b)$: choose $\xi(u)=2^{-1-v_2(b)}$. In either situation the forbidden set for row 3 produced by $(0,0,3)$ is invariant under $u$, with measure $2w_0-2h_0$. Both row 3 and its translate by $u$ avoid it. These two copies overlap by at most $2h_3$, since their covering arcs are half-turn translates of width $w_3+h_3\le1/2+h_3$. Thus
$$
 2w_0+2w_3\le1+2h_0+2h_3\le1+2D. \tag{1}
$$

In the remaining parallel case $v_2(b)>v_2(a)$ take $\xi(u)=2^{-2-v_2(a)}$. Then $2\psi(u)=0$ while $2\chi(u)=1/2$. The forbidden arc $F$ for row 5 from $(2,2,5)$ has width $l=2w_2-2h_2$ in the $2\chi$ phase. The covering set $B_5$ is invariant under $u$. Since $F$ misses row 5, the intersections of $B_5$ with $F$ and with $F+u$ each have measure at most $h_5$. The union of those two forbidden arcs has measure $\min(1,2l)$. We obtain $\min(1,2l)+w_5-h_5\le1$. Since $w_5>h_5$, this implies
$$
 4w_2+w_5\le1+4h_2+h_5\le1+4D. \tag{2}
$$

In case (1), replace the first baseline row by (1) and give the six rows the respective multipliers $(3/8,0,1/4,3/8,1/4,1/2)$. Complete the total demand on $w_4$ with $3/8$ of its width cap. This yields $2-D\le31/16+3D/4$, or $D\ge1/28$. In case (2), replace the last baseline row and use $(5/24,0,7/12,5/12,1/6,1/4)$, adding $5/8$ of the cap on $w_3$. Then $2-D\le31/16+D$, or $D\ge1/32$. Both contradict $D<1/80$. The sum of the six widths is therefore at most $159/80$. Integrating over the six translates gives the asserted volume bound $53/160$.

## Verification

Run `python3 verify.py` with the standard library to check the complete sextuple list, the six nondegeneracy duals, both final duals and the rational inverse margins. In the pinned Lean 4.33.1/Mathlib environment run `lake env lean SixRows.lean`. Five scalar declarations cover nondegeneracy, the margins for Grynkiewicz's hypotheses, both contradictions and the final division by six. The transference, self-sum inclusion and Haar measure arguments are written proofs. Neither this theorem nor its scalar formalization gives a two-sided estimate of the interval extremal function.
