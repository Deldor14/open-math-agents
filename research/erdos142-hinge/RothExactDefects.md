# Exact midpoint defects in near-optimal Roth sets

Write $R(n)=r_3(n)$ for the largest cardinality of a subset of $[n]=\{0,\ldots,n-1\}$ containing no nonconstant three-term arithmetic progression. In a free set $A$, a witness for the positive integer $d$ consists of **three distinct points** $x,y,z$ with $|x+z-2y|=d$. The choice of $y$ matters. It may lie outside the interval between $x$ and $z$. Let $\tau_A(d)$ be the fewest points of $A$ whose removal eliminates every witness for $d$.

**Every length.** Suppose $n\to\infty$, $H\to\infty$, $H=o(n)$, and $|A|=(1-o(1))R(n)$. Among the integers $1\le d\le H$, at least $(1/3-o(1))H$ satisfy
$$
\tau_A(d)\ge (1/4-o(1))R(n). \tag{1}
$$
Each such *individual* defect has at least $(1/12-o(1))R(n)$ witnesses on pairwise disjoint triples. One can also prescribe a list with repetitions from these defects and choose a disjoint triple for each entry, provided the list length is below the common cover lower bound divided by three. Indeed the vertices already used cannot meet all witnesses for the next entry. The defects that work can depend on $A$.

**When extremal density decreases.** Put $M=R(n)$ and
$$
\Delta(n)=1-\min_{n\le m\le 2n}\frac{nR(m)}{mM}.
$$
If $\Delta(n)$ stays bounded below by a positive constant, the conclusion strengthens. In **every** arithmetic progression of positive candidate defects of length $L\to\infty$ and maximum $T=o(n)$, all but $o(L)$ of its entries satisfy $\tau_A(t)\ge (\Delta(n)-o(1))M$. Both parities and arbitrary positive steps are allowed. The finite inequalities below also apply when $\Delta(n)$ tends to zero. They link a single exact defect to the density of the actual Roth number at every subsequent length through $2n$.

These statements concern the structure of large free sets. An explicit asymptotic equivalent for $R(n)$ is still missing. [Erdős problem 142, three-term variant](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/142.lean)

## Two shifts and the cost of coincident input points

For $t>0$ let $E_t$ be the set of smaller endpoints in $A$ of pairs at distance $t$, $2t$, or $t/2$ when the last is integral. For any covers $C,D$ of the respective defects $t,2t$,
$$
2|A|\le R(n+t)+2(|C|+|D|+|E_t|). \tag{2}
$$
Take $B=A\setminus(C\cup D\cup E_t)$. The two translates $B$ and $B+t$ are disjoint. A progression in their union projects onto a triple in $B$ of signed defect $0,\pm t$ or $\pm2t$. If all three projected points are distinct, the old progression-free condition and the two covers exclude every case. If precisely two are distinct, their distance is one of those charged to $E_t$. Finally two translates of a single point cannot contain a three-term progression. The union therefore has $2|B|$ points and fits in $[n+t]$.

For $t_j=b+qj$, $0\le j<L$, with $b,q\ge1$, there is a uniform estimate
$$
\sum_{j<L}|E_{t_j}|\le 3 |A| R(L). \tag{3}
$$
Fix the smaller endpoint $x$. For each of the three distance conditions, the possible indices are those admitting a $y\in A$ with $c y=u+vj$ for fixed integers $c,v>0$ and $u$. An arithmetic progression of indices would give an arithmetic progression of partners in $A$. This bounds each set of indices by $R(L)$ and summing proves (3).

There is an explicit exceptional-count version. If $T\ge\max_j t_j$ and $K+R(n+T)+4a\le 2|A|$ with $K>0$, at most $6|A|R(L)/K$ indices can have **both** $\tau_A(t_j)\le a$ and $\tau_A(2t_j)\le a$. On each such index (2) gives $K\le 2|E_{t_j}|$. The Lean theorem `rare_shifts` proves the finite bound for any chosen family of covers.

For $T=o(n)$ we have $R(T)=o(M)$. Indeed $R(2uv)\ge R(u)R(v)$ by the digit construction $x+2uy$ for independent free digit sets in $[u]$ and $[v]$. Take $u=T$, $v=\lfloor n/(2T)\rfloor$ and use $R(v)\to\infty$. Subadditivity gives $R(n+T)\le M+R(T)$. By (3) and Roth's theorem $R(L)/L\to0$, all but $o(L)$ of the indices have $|E_{t_j}|=o(M)$, uniformly for the progression under consideration. Thus on each remaining index the larger of $\tau_A(t_j),\tau_A(2t_j)$ is at least $(1/4-o(1))M$.

To count distinct values in $[1,H]$, take disjoint pairs $\{t,2t\}$ with
$$
 \frac{H}{4^{j+1}}<t\le\frac{H}{2\cdot4^j},\qquad j=0,1,2,\ldots.
$$
Their number is $H/3+O(\log(2H))$. The two endpoints for one band occupy a range disjoint from the endpoints for every other band. Within a band the lower and upper endpoints also occupy disjoint ranges. Applying (3) once over $[1,H]$ loses $o(H)$ pairs. This proves (1). A maximal family of disjoint triples always covers every witness by its union, proving the matching bound. The constant $1/3$ is sharp for this counting step alone. The doubling graph on $[1,H]$ consists of paths from odd roots, and the displayed matching pairs every other pair of vertices starting from the largest on each path. A path with $k$ vertices has minimum vertex cover $\lfloor k/2\rfloor$.

There is a finite kernel-checked version of the one-third count. Take $H=4^k w$ and let $G$ be the set of $d\in[1,H]$ whose chosen cover has more than $a$ points. For integers $K,a\ge0$ with $K+R(n+H)+4a\le2|A|$,
$$
 K H\le K w+3K|G|+18|A|R(H+1). \tag{8}
$$
The theorem `count_popular` constructs $(H-w)/3$ disjoint pairs. Within that matching, each pair whose two covers are small costs at least $K/2$ bad starts by (2). Every remaining pair supplies a different member of $G$. This also recovers (1) for arbitrary $H$ by restricting to $4^k\lfloor H/4^k\rfloor$, choosing $k$ large at fixed accuracy and then letting $H$ grow.

## Dilation from one exact defect

Remove a cover $C$ of $t$ and $E_t$, leaving $B$. For any $x,y,z\in B$, including repetitions,
$$
x+z-2y\in\{0,t,-t\}\quad\Longrightarrow\quad x=y=z. \tag{4}
$$
For this step only the distances $t,t/2$ need to be removed. Using the same $E_t$ facilitates (3).

Interpolate $R$ linearly between consecutive nonnegative integers and call the resulting function $P$. For every $\lambda>0$ and $n,t\ge1$, condition (4) yields
$$
P(\lambda)|B|\le R\big(\lceil\lambda(n-1+t)\rceil\big). \tag{5}
$$
Choose a real phase $c$ uniformly in $[0,t)$. For each input $x$ use the output integers $Y\equiv x\pmod t$ in the half-open interval $[\lambda x+c,\lambda x+c+\lambda t)$. These fibers are disjoint. For fixed $Y$, its possible inputs in its residue class lie in a half-open interval of length $t$, so there is at most one. Each fiber forms an arithmetic progression of $k$ or $k+1$ sites, $k=\lfloor\lambda\rfloor$. As $c$ moves over a full residue period, the mean count is $\lambda$. This follows by integrating the indicators of the equally spaced sites over that period, or by measuring the fractional part of the starting position in units of $t$. The probability of the larger count is therefore $\lambda-k$. Retain an optimal free subset of each fiber. The mean total retained is $P(\lambda)|B|$.

If three retained outputs formed a progression, their input defect would be divisible by $t$. All three output errors relative to $\lambda x+c$ belong to the same half-open interval of length $\lambda t$. Their second difference has absolute value strictly less than $2\lambda t$. Hence the input defect is $0$ or $\pm t$. By (4) the outputs belong to one fiber, where the retained set is free. The full configuration lies in a half-open interval of length $\lambda(n-1+t)$, which contains at most its ceiling in integer sites. Choosing a phase of at least average size proves (5). For integer $k\ge1$ there is also an explicit construction in $[kn+(k-1)t]$, using
$$
 x+t\big(\lfloor (k-1)x/t\rfloor+i\big),\qquad i\in S,\quad |S|=R(k),\ S\subseteq[k].
$$
The Lean theorem `single_defect_product` proves its injectivity, its progression-freeness and the stated interval bound.

Since $P(\lambda)=\lambda$ for $1\le\lambda\le2$, every integer $m\in[n,2n]$ satisfies
$$
 m|A|\le n R(m+2t)+m\big(\tau_A(t)+|E_t|\big). \tag{6}
$$
The companion Lean file proves (6) by an independent finite phase count. It assigns every $(x,r)\in B\times[mt]$ the phase $h=((m-n)x+r)\bmod(nt)$ and the output $Y=x+t\lfloor((m-n)x+r)/(nt)\rfloor$. The identity $nY+h=mx+r$ places each phase in the required tube. A progression projects to inputs satisfying (4) and the output fiber has at most two sites. Counting the injection over all $nt$ phases gives $m|B|\le nR(m+2t)$.

By subadditivity and the minimizing choice of $m$, (6) yields
$$
 \tau_A(t)\ge \Delta(n)M-(M-|A|)-R(2t)-|E_t|. \tag{7}
$$
Together with (3) and the digit bound, this proves the stated density-drop result. More generally, along any sequence with $0<\delta_n\le\Delta(n)$, if $M-|A|=o(\delta_n M)$, $R(2T)=o(\delta_n M)$ and $R(L)/L=o(\delta_n)$, all but $o(L)$ indices have $\tau_A(t_j)\ge(\Delta(n)-o(\delta_n))M$. Markov's inequality with threshold $M\sqrt{\delta_n R(L)/L}$ controls the last term in (7).

## An unconditional sequence with almost every individual defect

Write $f(n)=(\log n)^{-5/6}/\log\log n$. Infinitely many dyadic $n$ have $\Delta(n)\ge c f(n)$ for an absolute $c>0$. Indeed put $G(j)=\log(2^j/R(2^j))$. Subadditivity gives $0\le G(j+1)-G(j)\le\log2$, while the known upper bound on $R$ implies $G(J)\gg J^{1/6}/\log J$. Since $\sum_{j=2}^J j^{-5/6}/\log(j+2)\ll J^{1/6}/\log J$, infinitely many increments exceed a sufficiently small constant times $j^{-5/6}/\log(j+2)$. For $n=2^j$, the choice $m=2n$ gives $\Delta(n)\ge 1-\exp(-(G(j+1)-G(j)))$, at least half the increment. [Raghavan, version 3](https://arxiv.org/abs/2603.27045v3)

On these lengths, take any exact optimizer $A$. Uniformly in arithmetic progressions of candidate shifts of length $L\ge\exp((\log\log n)^8)$ and largest entry $T\le n/(\log n)^2$, all but $o(L)$ entries have $\tau_A(t)\gg f(n)M$. Thus each admits $\gg f(n)M$ disjoint three-point witnesses. For the error checks, the cited upper bound at $L$ gives $R(L)/L=o(f(n))$. Also the digit inequality gives $R(2T)/M\le 1/R(\lfloor n/(4T)\rfloor)\le(\log n)^{-2+o(1)}$ using $R(v)\ge v\exp(-O(\sqrt{\log v}))$. [Behrend-type lower estimate](https://arxiv.org/abs/2406.12290)

## Reproduction

Compile [RothDefects.lean](RothDefects.lean) followed by [RothExactDefects.lean](RothExactDefects.lean) in a Lean environment with the repository's mathlib, making the resulting modules available in the Lean search path. Then compile [RothDefectCount.lean](RothDefectCount.lean) and [RothDefectDilation.lean](RothDefectDilation.lean). The audit covers (2), (3), the finite one-third count (8), the exceptional-count bound, the projection argument for real dilations, the integer product inequality and the full rational inequality (6). The asymptotic deductions and the general real phase average in (5) are proved in the text.

Run `python3 check_roth_exact_defects.py` for finite independent checks. The script computes minimum covers by exhaustive search, constructs the rational fibers at each discrete phase, verifies progression-freeness and compares the dyadic matching size to the optimum on its path components. The earlier [packing note](RothDefectPacking.md) controls families of defects jointly and gives odd displacements on selected lengths with two- or three-point supports. Here the lower bounds on $\tau_A(d)$ concern one specified absolute defect at a time and require three distinct input points.
