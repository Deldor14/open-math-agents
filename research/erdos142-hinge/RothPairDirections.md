# Almost-perfect matching directions in an extremal Roth set

Let $A$ be a nonempty subset of $[n]=\{0,\ldots,n-1\}$ with no three distinct points in arithmetic progression. Write $m=|A|$, $M=R(n)=r_3(n)$ and $\rho=M/n$. Let $\tau(t)$ denote the minimum number of points of $A$ meeting all three-distinct-point witnesses $|x+z-2y|=t$. The choice of $y$ matters. For positive $t$, let $P_t$ count pairs at distance $t$ and put $u_t=m-2P_t$. The $t$-edges form a matching because two such edges at a vertex form a progression. Thus $u_t$ counts the unmatched vertices.

**Theorem.** Fix $0<\gamma<1$ and an exact optimizer $m=M$. Consider the entire set
$$
 E=\{1\le t\le n^{1-\gamma}:\ \tau(t)+\tau(2t)\le M\rho^2\}.
$$
As $n\to\infty$, it has the following properties, uniformly in the optimizer.

1. Its cardinality is at most $\log_{3/2}(n/M)+o(1)$, hence $O(\sqrt{\log n})$. For every other step in the range, one of its two specified defects has more than $M^3/(6n^2)$ witnesses on mutually disjoint triples of distinct points.
2. A fraction $1-o(1)$ of $A$ lies in disjoint translates of the **same** cube $\sum_{t\in E}\{0,t\}$. All its binary sums are distinct. Expanding every coordinate to $\{0,t,2t\}$ preserves injectivity, even across these different translates.
3. In an arithmetic progression of $L$ candidate steps, if $k$ of the steps belong to $E$, then $3^k\le(2k+1)(2k(L-1)+1)$. In particular $k\le\log_3 L+O(\log\log(3L))$.

The first conclusion concerns every sufficiently large length, with a bound on the *total number* of exceptional steps across a polynomial-size interval. The witness threshold $M^3/(6n^2)$ is $n^{1-o(1)}$ by the Behrend lower estimate. In a statement with any fixed $\beta>0$ it eventually exceeds $n^{-\beta}M/6$. All three conclusions apply to the corresponding smaller exceptional set as well.

## Small covers force matchings

Remove minimum covers of the two defects $t$ and $2t$ from $A$, leaving $B$. The [cluster inequality](RothDyadicClusters.md) gives $4|B|\le 3R(n+t)+2P_t(B)$ and $P_t(B)\le P_t$. It follows that
$$
 u_t\le 3(R(n+t)-m)+4(\tau(t)+\tau(2t)). \tag{1}
$$
This argument with arbitrary covers is compiled in [RothClusterCovers.lean](RothClusterCovers.lean). For a general finite estimate take distinct positive directions $t_1,\ldots,t_d$ with $u_{t_i}\le\delta m$ for all $i$. Suppose $d\ge1$ and put $\epsilon_d=2^d d(2d-1)\delta$. We will prove that if $\epsilon_d<1$ there is a union of disjoint full cubes of these directions covering at least $(1-\epsilon_d)m$ points, and
$$
 (3/2)^d(1-\epsilon_d)m\le n+\sum_i t_i\le 2n-1. \tag{2}
$$

## The two-direction graph

Fix two directions $s\ne t$. Their union of matched edges has degree at most two, with colors alternating. A simple path of four edges would have increments $e_1s,e_2t,e_3s,e_4t$, after exchanging colors if needed, where $e_i\in\{-1,1\}$. If $e_1=-e_3$ the fourth vertex is a $t$-neighbor of the first. It already has a $t$-edge to the fifth vertex, contradicting uniqueness. If $e_2=-e_4$, the second vertex has two different $s$-neighbors. Otherwise the first, third and fifth vertices form a nonconstant progression. This signed path calculation is checked in [RothClusterWindows.lean](RothClusterWindows.lean), theorem `alternating_path`.

Thus components are paths on at most four vertices or alternating four-cycles. In a four-cycle the signs on the two $s$-edges must be opposite, and likewise for $t$. Indeed a signed sum of two copies of each weight can vanish with nonzero coefficients only if $s=t$. Each cycle is therefore a square $\{a,a+s,a+t,a+s+t\}$. Every path has exactly two unmatched incidences across the two colors, including the isolated vertex counted twice. The number of vertices in components other than squares is at most $2(u_s+u_t)$.

## Finding simultaneous cubes

Let $G$ be the vertices matched in every chosen direction that belong to a square for every pair of directions. Counting the single-color misses and the nonsquare vertices gives
$$
 |A\setminus G|\le(2d-1)\sum_i u_{t_i}.
$$
On all of $A$, let $T_i$ swap the two ends of each $t_i$-edge and fix every unmatched point. Each $T_i$ is a permutation. At a matched vertex let $s_i(x)=(T_i x-x)/t_i$, either $1$ or $-1$. At a good vertex an $i$-move reverses sign $i$ and preserves every other sign by the square condition.

Fix an order on the $d$ moves. For every subset apply the indicated moves in this order. Each of the $2^d$ maps is a permutation, so at most $2^d|A\setminus G|$ starts have any such image outside $G$. From any remaining start every canonical path and all its prefixes are good. For each subset $I$ its endpoint is
$$
 x+\sum_{i\in I}s_i(x)t_i,
$$
with the starting signs flipped precisely on $I$. The sign vectors distinguish all the endpoints. The unique neighbor in direction $i$ at this endpoint is the endpoint for $I\mathbin{\triangle}\{i\}$, by the position and sign formulas. The cube therefore forms one whole orbit of the permutations. Cubes from different good starts coincide or are disjoint. Reorient each by its minimum $b$ to write it as $b+\sum_i\{0,t_i\}$. Their union contains at least $(1-\epsilon_d)m$ points. [Formal counting, sign and position lemmas](RothPairDirections.lean)

## Enlarging the digits

Write $w(V)=\sum_i V_i t_i$. Suppose $b+w(U)=c+w(V)$ for two cube minima and two ternary digit vectors. Every integer from $-2$ to $2$ has the form $X+Z-2Y$ with $X,Y,Z\in\{0,1\}$. Choose such a representation in each coordinate for $U_i-V_i$. We get
$$
 (b+w(X))+(c+w(Z))=2(c+w(Y)).
$$
All three points are in $A$, so they coincide. Disjointness of the binary cubes gives $b=c$ and faithfulness then gives $X=Y=Z$. Consequently $U=V$. The expanded cubes, each of size $3^d$, fit in $[n+\sum_i t_i]$ since their binary top vertices are at most $n-1$. The existence of even one faithful cube also gives $\sum_i t_i\le n-1$. Counting all the expanded cubes proves (2). The abstract injectivity and integer interval count are kernel-checked as `disjoint_ternary` and `ternary_volume`. [Lean source](RothPairDirections.lean)

In the exact case $u_{t_i}=0$ for all $i$, the cubes partition $A$, giving $2^d\mid m$ and $(3/2)^d m\le n+\sum_i t_i$. With $t_i=3^{i-1}$ and $A=\sum_i\{0,t_i\}$ the volume bound is attained. This binary cube is progression-free by uniqueness of base-three expansions in its midpoint equation. This example uses arbitrary progression-free $A$.

## Applying the finite bounds to an optimizer

Put $H=\lfloor n^{1-\gamma}\rfloor$. Subadditivity gives $R(n+H)-M\le R(H)$. The [digit construction](RothHeight.lean) gives $R(2Hv)\ge R(H)R(v)$ with $v=\lfloor n/(2H)\rfloor$. Thus $R(H)/M\le 1/R(v)\le n^{-\gamma+o(1)}$ using $R(x)\ge x\exp(-C\sqrt{\log x})$. Also $\rho\to0$ by Roth's theorem and $\rho\ge \exp(-C\sqrt{\log n})$ by the same lower estimate. [Behrend-type lower bound](https://arxiv.org/abs/2406.12290)

For every $t\in E$, (1) gives $u_t/m\le \delta=3R(H)/M+4\rho^2$. Take $D=\lceil\log_{3/2}(4/\rho)\rceil$. Uniformly for $1\le d\le D$ we have $\epsilon_d=o(1)$. Indeed $D=O(\sqrt{\log n})$ and $2^D=O(\rho^{-a})$ with $a=\log 2/\log(3/2)<2$. Thus $2^D D^2\rho^2\to0$, since $D=O(\log(2/\rho))$, and $2^D D^2 n^{-\gamma+o(1)}\to0$ as well. If $|E|\ge D$, select $D$ directions. The left side of (2) is at least $4(1-o(1))n$ while the right side is at most $2n-1$, an impossibility.

Now take **all** $d=|E|<D$ directions in (2). Their sum is at most $DH=o(n)$. The resulting inequality gives $d\le\log_{3/2}(n/M)+o(1)$ and the simultaneous cube covering asserted in the theorem. When $d=0$ the cubes are singletons and the assertions hold directly. For $t\notin E$ in the designated range, some defect has cover number $>M\rho^2/2$. The union of a maximal collection of disjoint witnesses is a cover of that defect, giving the count in part 1.

For a progression $b+qj$, $0\le j<L$, restrict to the $k$ directions in $E$ that it contains. Their ternary sums are all distinct by the cube conclusion. For ternary digits $a_i$, each value has the form $b\sum a_i+q\sum a_i j_i$. The two integer sums lie in $[0,2k]$ and $[0,2k(L-1)]$ respectively. This proves part 3. Taking logarithms first gives $k=O(\log(2L))$ (the $O(\log(2k))$ term is absorbed), and inserting this bound back yields the stated leading constant. The same proof works for any threshold $M\rho^p$ with fixed $p>\log 2/\log(3/2)$.

## Verification scope

The finite inequality with arbitrary covers (1) is formalized end to end. The written proof of (2) uses the kernel-checked path calculation, permutation-counting, sign, position and ternary-volume lemmas. The identification of the original graph components with cube orbits and the asymptotic application are proved in this text. The [independent Python checker](check_roth_clusters.py) also enumerates small progression-free sets and tests two-direction components and simultaneous ternary packing.
