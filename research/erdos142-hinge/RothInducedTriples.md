# Isolated arithmetic progressions and a short window for exact defects

Let $R(n)=r_3(n)$ denote the maximum size of a subset of $[n]=\{0,\ldots,n-1\}$ containing no nonconstant three-term arithmetic progression. Write $I(n)$ for the number of all such subsets, and $J(n)$ for the number **maximal under inclusion** in $[n]$. For a free set $A$, let $\tau_A(s)$ be the fewest points intersecting all witnesses $|x+z-2y|=s$ on three distinct points of $A$. We allow any ordering of $x,y,z$.

**A good length near every large starting point.** Fix $\epsilon>0$. Given a sufficiently large integer $N$, put $L=\lceil\log_2(32\log_2(2N))\rceil$. There is some $n=2^jN$, $0\le j\le L$, such that **every** free set $A\subseteq[n]$ of size at least $(1-1/(200L))R(n)$ satisfies
$$
 \tau_A(t)+\tau_A(2t)>\frac{R(n)}{200L}
 \quad\text{for every integer }1\le t\le\frac{n}{(\log\log n)^{1+\epsilon}}. \tag{1}
$$
For each such $t$, one of its two specified defects has more than $R(n)/(1200L)$ witnesses on mutually disjoint triples. The same $n$ works for all these sets and steps. Its position satisfies $N\le n\le64N\log_2(2N)$. The earlier conclusions for almost every logarithmic scale gave a larger cover fraction but allowed gaps between good lengths of unspecified size. [Earlier scale and coverage estimates](RothDyadicClusters.md)

**An obstruction to the Cameron–Erdős counting formula.** Suppose along a sequence that $t=o(n)$, that $|A|=(1-o(1))R(n)$ and that $\tau_A(t)+\tau_A(2t)=o(R(n))$. Then on those very lengths
$$
 \log_2 I(n)\ge\left(\frac{\log_2 7}{2}-o(1)\right)R(n),\qquad
 \log_2 J(n)\ge\left(\frac{\log_2 3}{2}-o(1)\right)R(n). \tag{2}
$$
The coefficients are about $1.4037$ and $0.7925$. Thus such a sequence would disprove the conjectured all-length estimate $\log_2 I(n)\sim R(n)$. The lower bound for $J(n)$ counts mutually incompatible choices whose maximal extensions all have size at least $(1-o(1))R(n)$. [Counting conjecture and published all-length upper bound](https://arxiv.org/html/2607.17746v1)

## A finite theorem

Let $m=|A|$, let $C,D$ cover defects $t,2t$ respectively, and put $c=|C|+|D|$. For any $t\ge1$ there exists an integer $p\ge0$ with all of the following properties:
$$
\begin{aligned}
 4m&\le3R(n+t)+2p+4c,\\
 7^p&\le I(n+t),&3^p&\le J(n+t),\\
 4p&\le R(2n+2t),&&\\
 3p&\le bR(\lceil(n+t)/b\rceil)&&\quad(b\ge1,\ b\nmid t).
\end{aligned}\tag{3}
$$
All of (3) is proved together in Lean, with the actual finite Roth number and the actual families of free and maximal sets. [Full finite theorem](RothInducedTradeoff.lean)

Remove $C\cup D$ to get $B$. Let $P=\{x:x,x+t\in B\}$ and $p=|P|$. The [two-defect cluster inequality](RothDyadicClusters.md) gives the first line of (3). The roots in $P$ have a stronger property than the original set:
$$
 x,y,z\in P,\quad x+z-2y=jt,\quad j\in\{-4,\ldots,4\}
 \quad\Longrightarrow\quad x=y=z. \tag{4}
$$
Here inputs may repeat. For details, distinct roots cannot differ by any of $t/2,t,3t/2,2t,3t,4t$. Order two roots as $a<b$. For gap $t$ or $2t$, the four available sites $a,a+t,b,b+t$ contain an ordinary progression. At gaps $t/2$ and $3t/2$ the triple $a,b,a+t$ has signed defect zero or $-2t$. At gaps $3t,4t$, the triple $a,a+t,b$ has defect $t,2t$. This list rules out any repeated-root counterexample to (4). When the roots are all distinct their two-site fibers are disjoint. For $|j|\le2$ use $x,y,z$ in $B$. For $j=3,4$ use $x,y+t,z$, and for $j=-3,-4$ use $x+t,y,z+t$. Each gives a forbidden triple on distinct points. [Kernel proof with all signs and repetitions](RothInducedTriples.lean)

Replace each pair by the three sites $x,x+t,x+2t$. The enlarged set $U$ is contained in $[n+t]$. Its fibers are disjoint by (4), since a collision gives a difference of at most $2t$ in integer multiples of $t$. A progression of three sites projects to roots with defect $jt$, $|j|\le4$. Thus **all the nonconstant progressions in $U$ are precisely the $p$ disjoint three-site fibers**. The independence polynomial on $U$ is $(1+3z+3z^2)^p$. Each choice of at most two sites per fiber gives a free set. Choosing exactly two gives $3^p$ sets of size $2p$. Different such choices cannot extend to the same free set, as their union contains a whole fiber. Extending them to maximal sets proves the two counting estimates. [Count of all subsets](RothInducedCount.lean) · [Distinct maximal extensions](RothMaximal.lean)

For $b\nmid t$ each residue class mod $b$ in $U$ is free because no full fiber lies in it. Rescale each class by subtracting the residue and dividing by $b$. Each then occupies at most $\lceil(n+t)/b\rceil$ sites, giving the last line of (3). In particular, if $n+t\le KN$ and $(K+B_0)R(N)<3p$, every $1\le b\le B_0$ divides $t$. Indeed partition each rescaled interval into $\lfloor K/b\rfloor+1$ blocks of length $N$. The number of charged blocks across all classes is at most $K+b$. [Residue inequality](RothInducedScales.lean) · [Simultaneous divisibility criterion](RothInducedWindow.lean)

For the doubling estimate take four outputs per root,
$$
 x+t\bigl(\lfloor x/t\rfloor+i\bigr)=2x-(x\bmod t)+it,\qquad i\in\{0,1,3,4\}.
$$
They are congruent to $x$ modulo $t$. A progression of outputs has input defect $jt$ by congruence. Each error relative to $2x$ lies in $(-t,4t]$, so the absolute second difference of these errors is strictly less than $10t$, giving $|j|<5$. By (4) all roots coincide, and $\{0,1,3,4\}$ is free. The same projection with two coincident outputs proves injectivity. Each root has $x+t<n$, giving the containing interval in (3). [Four-point construction](RothInducedDoubling.lean)

## The bound on gaps between good lengths

Write $n_j=2^jN$, $M_j=R(n_j)$ and $H_j=\lfloor n_j/(\log\log n_j)^{1+\epsilon}\rfloor$. Uniformly over $j\le L$,
$$
 R(2H_j)/M_j=o(1/L). \tag{5}
$$
In fact the digit bound $R(2uv)\ge R(u)R(v)$ at $u=2H_j$, $v=\lfloor n_j/(4H_j)\rfloor$ gives $R(2H_j)/M_j\le1/R(v)$. Here $v\gg (\log\log N)^{1+\epsilon}$ and $R(v)\ge v^{1-o(1)}$; also $L$ is of order $\log\log N$. Use $R(a+b)\le R(a)+R(b)$ throughout. [Digit inequality](RothHeight.lean) · [Behrend-type lower estimate](https://arxiv.org/abs/2406.12290)

Suppose every scale fails (1) and choose one witnessing set and one step at each scale. Then $m_j\ge(1-1/(200L))M_j$ and $c_j\le M_j/(200L)$ using minimum covers. For large $N$ take the bound in (5) at most $1/(1000L)$. The first line of (3) gives
$$
 2p_j\ge (1-43/(1000L)) M_j .
$$
The third line of (3), and the cost at most $R(2H_j)$ to return to length $2n_j$, give $M_{j+1}\ge2(1-1/(20L))M_j$ for $j<L$. Put $Q=2^L$. Bernoulli's inequality yields $M_L\ge(19/20)QM_0$. Hence $3p_L\ge(3/2)(19/20)^2 Q M_0>(5/4)QM_0$.

For large $N$, $n_L+t_L\le(9Q/8)N$. Apply the divisibility criterion at the terminal scale with $K=9Q/8$ and $B_0=Q/8$. Both are integers and every $b\le Q/8$ must divide $t_L$. For $s=Q/8$, $\operatorname{lcm}(1,\ldots,s)\ge 2^s/(s+1)$. Each binomial coefficient $\binom{s}{i}$ divides this lcm, since each prime-power term in its factorial valuation is 0 or 1 and only powers at most $s$ can contribute. The largest coefficient is at least the average. Now $4\log_2(2N)\le s<8\log_2(2N)$, so $2^s/(s+1)>QN$ eventually. This contradicts $0<t_L\le n_L=QN$. Finally a maximal family of disjoint witness triples covers all witnesses by its union. This proves (1) with the claimed disjoint count.

The entire finite window argument, including the quantifier order, has a kernel-checked version. Put $L=k+3$, $M_j=R(2^jN)$, and choose integer bounds $H_j$. If $M_0>0$, $H_L\le 2^kN$ and $(2^k+1)H_L<2^{2^k}$, some $j\le L$ works for every $A,C,D,t$ from (3) on that scale with $1\le t\le H_j$. It satisfies
$$
 M_j < 80L\bigl(M_j-|A|+|C|+|D|+R(2t)\bigr).
$$
This form has finite, evaluable conditions. Under (5), the size and cover thresholds used above make the right side at most $80(1/200+1/200+1/1000)M_j<M_j$ at a failing scale. [Lean theorem `exists_good_scale`](RothInducedRun.lean)

There is also a two-scale conclusion. For $t,s=o(n)$ with $s$ odd, let $c_1$ be the two-cover cost in any near optimizer on $[n]$ at $t$, and $c_2$ its counterpart for any near optimizer on $[2n]$ at $s$. Formula (3) gives $R(2n)\ge2R(n)-8c_1-o(R(n))$. At the second length its modulus $b=2$ gives $3(R(2n)-4c_2)/2\le2R(n)+o(R(n))$. Therefore $12c_1+6c_2\ge(1-o(1))R(n)$. In particular one of $c_1/R(n),c_2/R(2n)$ is at least $1/24-o(1)$. The parity restriction is only on the step at the longer length.

## Counts at the original length

For (2), remove the final $t$ sites of the initial interval before applying (3). This costs at most $R(t)=o(R(n))$ by the digit inequality, since $t=o(n)$. At the new input length $n-t$ the enlarged fibers fit in $[n]$ itself. The first line of (3) gives $2p\ge(1-o(1))R(n)$, proving (2). Quantitatively, if the Cameron–Erdős formula holds at a sequence of lengths, this calculation gives
$$
 \tau_A(t)+\tau_A(2t)\ge
 \left(\frac{1-2/\log_2 7}{4}-o(1)\right)R(n)
$$
there for every $t=o(n)$ and every near optimizer on those lengths.

Without any hypothesis on the initial optimizer, we also obtain the all-length lower bound
$$
 J(n)\ge3^{R(\lfloor n/5\rfloor)} . \tag{6}
$$
Start with an optimal free set $S\subseteq[\lfloor n/5\rfloor]$. Put a triple $5u,5u+1,5u+2$ above each $u\in S$. In a midpoint equation the digit defect has absolute value at most four. Divisibility by five forces it to vanish, so all roots coincide. The incompatible maximal extensions above give (6), including lengths less than five. [Formal all-length theorem](RothMaximal.lean)

In particular $\log J(n)=\Theta(R(n))$ at every sufficiently large length. For the lower bound $R(n)\le5R(\lfloor n/5\rfloor)+4$ by interval partition. For the upper bound $J(n)\le I(n)\le2^{O(R(n))}$ by Morris, Ortega and Rué. On a set of lengths of logarithmic density one, our previous container estimates also give $J(n)\le(1.671)^{(1+o(1))R(n)}$. Every maximal free set in a container is maximal inside its induced three-uniform hypergraph. Apply the Lonc–Truszczyński bound with base less than $1.671$ in each of the $\exp(o(R(n)))$ containers of size at most $(1+o(1))R(n)$. On these lengths inclusion-maximal sets therefore form an exponentially small fraction of all free sets. [All-length counting upper bound](https://arxiv.org/html/2607.17746v1) · [Container estimates on typical lengths](RothEntropy.md) · [Maximal sets in a three-uniform hypergraph](https://scholars.uky.edu/en/publications/on-the-number-of-minimal-transversals-in-3-uniform-hypergraphs/)

The elementary lower construction also gives $J_k(n)\ge k^{r_k(\lfloor n/(2k-1)\rfloor)}$ for each fixed $k\ge3$, with $J_k$ defined using $k$-term progressions. Use radix $2k-1$ and digits $0,\ldots,k-1$. Every consecutive triple in an output progression has digit defect of magnitude at most $2(k-1)<2k-1$. Thus its roots form a $k$-term progression and coincide by freeness. Each fiber admits $k$ incompatible choices omitting a single site. Together with the same all-length counting upper bound this yields $\log J_k(n)=\Theta_k(r_k(n))$.

## Reproduction and scope

The finite assertions (3), (4), (6), the simultaneous-divisibility criterion and the finite good-scale theorem including the dyadic iteration are checked by Lean. The passage to the logarithmic range in (1), the asymptotic counting consequences and the extension to general $k$ are proved in the text. Compile the sources in dependency order starting with the [previous cluster proofs](RothDyadicClusters.md). After `RothInducedTriples`, compile `RothInducedCount`, `RothInducedScales` and `RothInducedDoubling`. Then compile `RothMaximal`, `RothInducedWindow` and `RothInducedTradeoff`, followed by `RothInducedRun`. The [independent Python checker](check_roth_induced.py) enumerates small intervals, full independence polynomials, residue restrictions, four-site expansions and maximal extensions. The explicit growth equivalent for $r_3(n)$ required in Erdős 142 remains open.
