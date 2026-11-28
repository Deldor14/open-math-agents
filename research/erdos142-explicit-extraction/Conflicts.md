# Roth sets with prescribed vertices and an arbitrary conflict graph

Let $V\subseteq[1,N]$ and let $G$ be any simple graph on $V$, with degrees $d_x$. Write $A=(17-6\sqrt2)/28$, $a_0=\log(1/A)$, $\beta_*=0.17067648186\ldots$, and
$$
 z_N=0.12716\,(\log N)^{\beta_*}\exp(-2\sqrt{a_0\log N}).
$$
There is a deterministic algorithm returning a set $I\subset V$ that contains neither a nonconstant three-term arithmetic progression nor an edge of $G$, with
$$
 |I|\ \ge\ (1-o(1))\sum_{x\in V}\frac{z_N}{1+d_xz_N}.
 \tag{1}
$$
The error is uniform in $V,G$ as $N\to\infty$. Given an edge list the time bound is $(N+|E(G)|)N^{o(1)}$ bit operations. The constant comes from the [local-curvature result](https://github.com/Deldor14/open-math-agents/tree/c116f738b0666742b239f51404784a1a31621e32/research/erdos142-local-curvature) and its [finite extraction](Curved.md). The exponent belongs to [zeemy23](https://github.com/zeemy23/open-math-agents/blob/8854e183a6466b5a14e166ab82e437ef7b500950/research/erdos142/torus-bound/LowerBound.md).

In particular, let $P,T\subseteq[1,N]$ be disjoint, with $P$ progression-free, $|P|=o(1/z_N)$ and $|T|=o(N)$. In $N^{1+o(1)}$ bit operations one can construct an ordinary progression-free subset of $[1,N]$ of size at least $(1-o(1))Nz_N$, containing *all* of $P$ and avoiding *all* of $T$. The earlier [prescribed-site estimate](https://github.com/Deldor14/open-math-agents/blob/e6b1de687accea73a7ae40634cf0878d6930ede4/research/erdos142-hinge/RothExtensions.md) retains $(1-o(1))r_3(N)$ when $|P|=o(N/r_3(N))$. It uses the actual extremal number. The present constructive guarantee gives a different tradeoff between the allowed number of pins and the promised size. Neither statement determines the ratio-one formula for $r_3(N)$.

For another consequence, partition any subset of $[1,N]$ into classes with sizes $h_i$. There is an AP-free partial transversal meeting at least $(1-o(1))\sum_i h_i z_N/[1+(h_i-1)z_N]$ classes, with at most one site in each. Use a disjoint union of cliques. If $\min_i h_i z_N\to\infty$, this hits a $1-o(1)$ fraction of all classes, for any such partition.

## A graph inequality and its finite Roth-number version

Minimum-degree greedy selection in a finite graph $H$ attains at least the Caro–Wei sum $\sum_{x\in H}1/(1+\deg_H x)$. Indeed, choosing a minimum-degree vertex and deleting its closed neighborhood removes a sum of at most one, and the other reciprocal terms can only increase upon deletion. The procedure constructs an independent set. With a heap, restricting an input graph to a subset and making these choices takes $O((N+|E|)\log(N+1))$ elementary operations.

There is also a finite bound in terms of the genuine extremal number, without any asymptotic lower-bound construction. Let $q>N$ be an odd prime and $S\subseteq\mathbb Z/q$ any nonempty set free of proper modular progressions, of size $s$. Some progression-free graph-independent subset of $V$ has size at least
$$
 \sum_{x\in V}\frac{s/q}{1+d_x(s-1)/(q-1)} . \tag{2}
$$
Choose a uniform invertible affine map of the prime field. Its pullback of $S$ to $V$ is progression-free since distinct indices remain distinct. Each vertex occurs with probability $s/q$, and conditional on its occurrence each other vertex occurs with probability $(s-1)/(q-1)$ by two-transitivity. Apply the graph inequality conditionally at each vertex and Jensen's inequality to the reciprocal. The right side can be attained or exceeded by trying the $q(q-1)$ affine maps and running the stated greedy rule. In particular take an optimal ordinary $S$ in $[1,N]$ and the first prime $q>2N$. Its modular image is progression-free because an integer second difference has magnitude less than $2N$. This gives (2) with $s=r_3(N)$ as an existence theorem. For example, when $\min_{x\in V} d_x r_3(N)/N\to\infty$, (2) approaches $\sum_{x\in V}1/(d_x+1)$ in relative error, uniformly. Here $q=O(N)$ already follows from Bertrand’s postulate.

## The degree-by-degree finite estimator

Use the earlier selection of $m$, $M$, box features, marked score and energy window. For its good choice of window and score, the exact reference one-site probability $p$ exceeds $z_N$ for all sufficiently large $N$, by the strict source comparison $0.1271607636856\ldots>0.12716$. Three distinct sites forming a progression simultaneously qualify with probability $p_3\le p\,o(1/N)$, uniformly. For **two** distinct indices their phases under the reference Haar affine law are independent uniform on the torus. Thus their reference acceptance probability is exactly $p^2$, irrespective of their difference. This holds block by block, including conditional continuation from two possibly different prefix colours. The finite one-block pair law is dominated by $(1+\eta)$ times its reference law, with $\eta=1/(m+1)^2$. Indeed one may marginalize the three-cell calculation before discarding invalid sites: the joint law of the first and middle cells is precisely the pair law, even if the extrapolated third index lies outside $[1,N]$. Its proof uses only that the first two indices have a nonzero difference of magnitude below $N$.

Given a fixed candidate parameter, compute $p$ exactly from its single-site convolution. Put $t_x=d_xp$,
$$
 a_x=\frac{1+2t_x}{(1+t_x)^2},\qquad b_x=\frac1{(1+t_x)^2}.
$$
Convexity of the reciprocal, or completing a square, gives
$$
 \frac1{1+k}\ \ge\ a_x-b_x k\quad(k\ge0).
$$
Round $a_x$ down and $b_x$ up to a common dyadic denominator at least $(N+1)^{10}$. Denote the rounded quantities by $\bar a_x,\bar b_x$. For any fixed shell pullback let the payoff be the sum of $\bar a_x$ over qualifying $x\in V$, minus one $\bar a_y$ for each qualifying ordered proper AP with middle $y$ in $V$ and both endpoints in $V$, minus $\bar b_x+\bar b_y$ for each qualifying edge $xy$. On erasing all occupied middles in these triples, the surviving positive sum is at least its first two terms. The total edge penalty can only decrease. Minimum-degree greedy selection on the survivors has size at least the payoff by the pointwise tangent inequality.

At a prefix with $r$ blocks unchosen, use reference continuation probabilities in all three sums. Multiply the positive sum by $(1-\eta)^r$ and both negative sums by $(1+\eta)^r$. The average of the next estimator under the finite affine alphabet is at least the present one. The proof is the nonnegative atom comparison for singles, pairs and triples, separately for each weighted term. The rounding loss in the initial estimator is $O((N+1)^{-8})$, as there are at most $N^2$ terms of each kind and $m\eta=o(1)$.

Let $B=\sum_{x\in V}p/(1+d_xp)$. At the empty prefix the unrounded positive term minus the edge penalty under Haar is exactly $B$, since
$$
 p a_x-p^2d_x b_x=\frac p{1+t_x}.
$$
The positive term is at most $2B$ since $(1+2t_x)/(1+t_x)\le2$. The edge term is at most $B$. At a fixed middle $y$ there are at most $N$ ordered proper triples. Thus their total expected weighted penalty is $o(1)\sum_y a_y p=o(B)$. The factors $(1\pm\eta)^m$ introduce another $o(B)$ uniformly even for a dense graph. For nonempty $V$ the rounding error is $o(B)$ because $p\ge z_N=N^{-o(1)}$ and $B\ge p/(1+Np)\gg1/N$. This proves that the best initial parameter has estimator at least $(1-o(1))B$, implying (1) by monotonicity in $p$. Empty $V$ has the empty answer. Fix successive blocks by deterministic maximization as in the original proof. Its final graph payoff is bounded by the size the greedy rule actually returns.

For computation, weight the coefficient sum at each occupied middle by its integer numerator for $\bar a_y$ when forming the prefix triple histogram. Subtract the similarly weighted diagonal. The indicator polynomials themselves still have zero-one coefficients, so the packed products are unchanged. For edges, enumerate the supplied list once per evaluation and accumulate the two vertex numerators by the two prefix colours. The pair continuation is a product of the two single-colour continuation probabilities. All weights have $O(\log N)$-bit numerators after rounding. The number of parameters and states remains $N^{o(1)}$. These operations and the preceding finite algorithm yield the stated time bound. The implementation includes a singleton fallback whenever $V$ is nonempty.

## Extending a prescribed set

Remove the prescribed and excluded vertices from the ground set, together with every possible completion of two distinct elements of $P$. The latter excludes at most $3\binom{|P|}{2}$ vertices. Join two remaining vertices if they form a progression with one member of $P$. For each vertex and each pin there are at most three choices for its neighbor. Thus the maximum degree is at most $3|P|$. For every AP-free graph-independent output, adjoining $P$ yields a free superset of $P$ missing $T$. Conversely any free extension avoiding $T$ induces exactly these constraints on its new vertices. The remaining ground set has size $(1-o(1))N$ and $|P|z_N\to0$ under the stated hypotheses, so (1) gives the claimed coefficient. The same proof gives the finite lower comparison (1) for the actual degrees of this graph when the numbers of pins or forbidden sites are larger. Constructing it costs $O((N+1)(|P|+1)+|P|^2)$ elementary operations. All statements here concern unrestricted integer progressions in the returned set.

## Reproduction

graph.py reads either a JSON input with N, vertices and edges or one with N, required and excluded, followed by the path to the two original polygon modules. It uses the same theoretically large mesh as curved.py. Run the finite tests with:

    python3 check_graph.py

The independent check covers all 1,024 graphs on five vertices and the 110 invertible affine maps modulo 11, weighted prefix counts and 1,622 comparisons of prescribed extensions. Three finite conditional-expectation examples include positive pins. GraphTangent.lean checks the tangent, its exact per-vertex expectation and the bound on the positive cost. The asymptotic result combines these finite arguments with the written endpoint extraction proof.
