# Packing near progressions in every extremal Roth set

Let $[n]=\{0,\ldots,n-1\}$, let $R(n)=r_3(n)$, and write $D(x,y,z)=x+z-2y$. Fix positive integers $s,t$. On a three-term-progression-free set $A\subseteq[n]$, form the hypergraph whose edges are **three distinct** elements admitting an ordering with
$$ D(x,y,z)=jt,\qquad 1\le |j|\le 2s. \tag{1} $$
The designation of $y$ is part of the witness. For $t=1$ one can always put the three points in increasing order: if the designated point was exterior, the diameter is at most the original absolute defect, and putting the middle point in the middle gives a nonzero defect at most that diameter. For general $t$ reordering may change the congruence.

**All-length packing.** If $|A|=R(n)=M$ and $st\le n$, every inclusion-maximal family of disjoint edges covers all but at most
$$ \frac{2R(n+st)}{R(s+1)}\le\frac{4M}{R(s+1)} \tag{2} $$
points. Thus even if $s$ tends to infinity arbitrarily slowly, the covered proportion tends to one, uniformly in $t\le n/s$ and in the choice of extremizer. For example, one may take $t=1$ and $s=\lceil\log\log n\rceil$ at large $n$. The matches then consist of genuine ordered triples whose two consecutive gaps differ by at most $2s$. The theorem controls the mismatch of the gaps and makes no requirement on their common scale.

## The two copies and the digit construction

The simplest example of the obstruction is the union of $2A$ and $2A+t$ for odd $t$. Put $T_A(d)=\#\{(x,y,z)\in A^3:D(x,y,z)=d\}$. The number of ordered nonconstant progressions in the union is exactly $T_A(t)+T_A(-t)$. Parity places both endpoints on the same sheet, and a progression using a single sheet would already be present in $A$. This identity also counts configurations with repeated projections onto $A$. The following argument removes that ambiguity for (2).

Let $B\subseteq A$ contain no edge and put $d=t/\gcd(t,2)$. Take the first, third, fifth and subsequent odd-indexed elements of each ordered list of $B$ in a residue class modulo $d$. This retains a set $C$ of size at least $|B|/2$. To check repeated coordinates, call an unordered pair at distance $h>0$ forbidden if either $t\mid h$ and $h\le2st$, or $t\mid 2h$ and $h\le st$. Both points occur on the same list. They must be consecutive on it:

* In the first case any intervening list element can serve as center. The endpoints are congruent modulo $t$ and twice the center is congruent to twice either endpoint. The absolute defect is at most $h$.
* In the second case there are at most two residues modulo $t$ on that list. Of the three points, two have the same residue modulo $t$. Use them as endpoints. Twice the third is congruent to twice either endpoint, and the absolute defect is at most $2h$.

In either case an intervening point would give an edge, since a zero defect on three distinct elements is excluded already. Thus $C$ contains no forbidden pair. Every solution in $C$, allowing repeated coordinates, of $D(x,y,z)=jt$, $|j|\le2s$, now has $x=y=z$ and $j=0$.

Choose an optimal progression-free $U\subseteq[s+1]$. The map $(x,u)\mapsto x+tu$ on $C\times U$ is injective: a collision would give $D(x,y,y)=(v-u)t$. A progression in its image would give $D(x,y,z)=(2v-u-w)t$, with $|2v-u-w|\le2s$. The preceding conclusion forces the first coordinates to coincide and $u+w=2v$. Then the digits coincide as well. The image lies in $[n+st]$, so $|B|R(s+1)\le2R(n+st)$. The points missed by any maximal matching are such a $B$. Subadditivity gives (2).

## Size of the largest set avoiding these defects

Write $S(n;s,t)$ for the largest cardinality in $[n]$ avoiding both ordinary progressions and (1) on distinct points, and put $m=\min(n,\lceil n/s\rceil+t)$. For all positive $n,s,t$,
$$ \frac16 R(m)\ \le\ S(n;s,t)\ \le\ 2R(m). \tag{3} $$
Thus the transition at $t$ of order $n/s$ is controlled by the ordinary finite Roth number. The constants in (3) are absolute.

For the upper bound compress each point by
$$ P(a)=a-t\left\lfloor\frac{(s-1)a}{st}\right\rfloor . $$
It has the same residue modulo $t$ and satisfies $a/s\le P(a)<a/s+t$. Also $0\le P(a)\le a$, so its image lies in $[m]$. The errors $a-sP(a)$ all belong to $(-st,0]$. Three distinct preimages whose images have zero defect would have an input defect divisible by $t$ and of absolute value strictly less than $2st$. This excludes three distinct preimages in a single fiber, and excludes a progression on three different image points. Hence the image has at most $R(m)$ points and each fiber has at most two.

For the first lower construction put $L=2s+2$, take an optimal set in $[\lceil n/L\rceil]$, and map its elements by
$$ Q(b)=b+t\left\lfloor (L-1)b/t\right\rfloor. $$
This map is strictly increasing, preserves the residue modulo $t$ and satisfies $Lb-t<Q(b)\le Lb\le n-1$. If an output defect were divisible by $t$ with magnitude at most $2st$, the input defect would also be divisible by $t$. Its magnitude would be strictly less than $(2s+2)t/L=t$, as the three rounding errors are in $(-t,0]$. The input would therefore form a progression. A second lower construction takes an ordinary optimal set in $[\min(n,\lceil t/2\rceil)]$, whose defects all have magnitude less than $t$. Put $a=\lceil n/L\rceil$ and $b=\min(n,\lceil t/2\rceil)$. Then $m\le4a+2b$ since $L\le4s$. Subadditivity gives $R(m)\le4R(a)+2R(b)\le6 S(n;s,t)$.

For a **fixed** extremizer $A$ and $st\le n$, its maximum edge-free subset has size between $M/(4s+2)$ and $4M/R(s+1)$. The upper bound is (2)'s argument; for the lower bound average over all translates of a block of $\lceil t/2\rceil$ consecutive residues modulo $(2s+1)t$. Inside such a block every lifted defect has, modulo $(2s+1)t$, a representative of magnitude strictly less than $t$. If it is divisible by $t$ this representative is zero. None of the nonzero multiples in (1) are zero modulo $(2s+1)t$. Thus any one block is edge-free, and its average population gives the stated bound. The Behrend lower estimate $R(s)=s^{1-o(1)}$ makes the maximum edge-free fraction $s^{-1+o(1)}$, uniformly as $s\to\infty$. [Behrend-type constructions](https://arxiv.org/abs/2406.12290)

There are also at least $M R(s+1)^2/108$ distinct unordered edges in $A$ whenever $R(s+1)\ge6$ and $st\le n$. Indeed write $K=4M/R(s+1)$. Retain vertices independently with probability $p=3K/(2M)\le1$ and delete one vertex from every surviving edge if needed. The resulting independent set has expected size at least $pM-p^3 e$, where $e$ is the number of edges. Its size is at most $K$, so $e\ge4M^3/(27K^2)$.

## Prescribing one absolute defect on selected lengths

There is an absolute $c>0$ and an infinite sequence of $n$ for which every extremizer $A$ exhibits **every positive odd absolute defect** up to $cn f(n)$, where
$$ f(n)=\frac{1}{(\log n)^{5/6}\log\log n}. $$
For each such odd $t$ there are at least $cM f(n)$ configurations of absolute defect $t$ on pairwise disjoint supports in $A$. Here a support can have two or three points. Even a two-point support gives a genuine nonconstant progression among the lifted points of $2A\cup(2A+t)$.

To see this put $g(n)=\log(n/R(n))$, $v_j=j^{-5/6}/\log(j+2)$, $\sigma_j=\epsilon v_j$, and start a sequence at $n_2=4$, with $n_{j+1}=2n_j+\lfloor\sigma_j n_j\rfloor$. For any fixed $0<\epsilon\le1$, $\log n_J\sim J\log 2$. The upper bound of Raghavan gives $g(n_J)\ge c_0 J^{1/6}/\log J$ for all large $J$, with $c_0>0$ chosen independently of $\epsilon$. Also $\sum_{j\le J}v_j\le C J^{1/6}/\log J$, by splitting at $\sqrt J$ and summing $j^{-5/6}$ in each part. Choose $\epsilon$ so that $2C\epsilon<c_0/2$. [Raghavan, version 3](https://arxiv.org/abs/2603.27045v3)

Let $u_j=\log(2R(n_j)/R(n_{j+1}))\le\log 2$. The identity
$$ g(n_{j+1})-g(n_j)=u_j+\log(n_{j+1}/(2n_j)) $$
and $\log(n_{j+1}/(2n_j))\le\sigma_j$ imply that at least $\gg J^{1/6}/\log J$ indices $j<J$ have $u_j\ge\sigma_j$. On each such index take any positive odd $t\le\sigma_j n_j$. From a maximal disjoint family of supports witnessing $|D|=t$, remove all used points, leaving $B$. By the two-copy identity $2B\cup(2B+t)$ is progression-free. Its $2|B|$ points fit in $[n_{j+1}]$, giving $|B|\le R(n_j)e^{-\sigma_j}$. Each support has at most three points. Since $v_j\asymp f(n_j)$, decreasing $c$ proves both assertions. This use of an upper bound for $R$ differs from the all-length matching (2), which follows solely from the finite construction.

The [companion note](RothDefectSpectrum.md) gives an asymptotic count on another range of scales and a Fourier consequence. The [Lean file](RothDefects.lean) verifies the injective digit expansion for mathlib's finite Roth number, the even-modulus thinning step and three supporting identities and inequalities. The full matching, rounding and asymptotic arguments are written proofs. The [finite checker](check_roth_defects.py) tests the thinning at even and odd $t$, both rounding maps and the exact two-copy formula. These results concern approximate midpoint equations. The asymptotic formula for the ordinary $R(n)$ in [Erdős problem 142](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/142.lean) remains open. Related work on approximations with an error proportional to the gap uses a different approximation condition. [Fraser–Shmerkin–Yavicoli](https://arxiv.org/abs/1910.10074)

