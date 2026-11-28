# Sharp padding in adaptive interval covers for the Roth number

Write $R(N)=r_3(N)$. For every integer $n\ge1$,
$$
 R(32n+35)\le 32R(n),\qquad R(62n+73)\le 62R(n).
$$
Every three-term-progression-free set in the indicated interval can actually be covered by the stated number of contiguous $n$-point intervals. For the first bound with $n\ge8$, and the second with $n\ge11$, increasing the input length by one already permits a set needing an additional interval. Sharpness concerns the covering assertion. The cardinality inequalities may persist farther.

There is a common formula behind these examples. It connects the cover length to avoidance of adjacent blocks having equal lengths and sums. It also gives an asymptotic constant for this particular covering problem. All progressions in the statement about $R$ are ordinary integer progressions.

## Exact fixed-block threshold

Let $g(q)$ be the least total weight of a word of $q$ nonnegative integers that contains no two adjacent nonempty blocks of equal length and equal sum (an *additive square*). Such words exist at every length, for example with distinct successive powers of two. Write $H(q,n)$ for the greatest interval length for which every AP-free subset can be covered by $q$ contiguous $n$-point intervals. Then
$$
 H(q,n)\ge qn+g(q),\qquad H(q,n)=qn+g(q)\quad\text{if } n>g(q). \tag{1}
$$

To prove the lower bound, greedily cover the smallest uncovered point by an $n$-point interval starting there. A failure produces $q+1$ increasing original points $x_0,\ldots,x_q$ with successive differences at least $n$. Conversely such a list cannot fit in $q$ covers, since each interval contains at most one listed point. If covers must stay inside the ambient interval, the last greedy interval may be shifted back to its right boundary without losing any point that still needed coverage.

Write the successive differences as $n+e_i$. Two adjacent equal-length groups with equal sums of $e_i$ would give a three-term progression in the selected points. Thus the span is at least $qn+g(q)$ and the list needs an interval of at least $qn+g(q)+1$ points.

For the converse take a minimizing word, put $P_0=0$, $P_i=e_1+\cdots+e_i$, and take $x_i=1+ni+P_i$. For $i<j<k$ an endpoint equality would force
$$
 n(i+k-2j)=2P_j-P_i-P_k .
$$
The right side is the difference of two disjoint nonnegative block weights and has absolute value at most $g(q)$. If $n>g(q)$ the index coefficient must vanish. The remaining equality is an additive square. Hence these $q+1$ points disprove covering on the next length.

The same witnesses often work at much smaller $n$. For the certified 32-letter and 62-letter witnesses, evaluating the equation above for every index triple gives largest conflicting positive lifts 7 and 10 respectively. This supplies the sharper uniform ranges in the opening statement.

## Linear growth of the padding

The limit $\gamma=\lim_{q\to\infty}g(q)/q$ exists. The following are explicit bounds:
$$
 \frac{73}{61}\le\gamma\le\frac{37}{20}.
$$
Equivalently $\gamma$ is the iterated limit of $(H(q,n)-qn)/q$, first in $n$ and then in $q$. No exchange of limits is needed.

Restriction to adjacent pieces gives superadditivity of $g$. Grouping an admissible word of length $ab$ into $a$ blocks of length $b$ gives the stronger
$$
 g(ab)\ge a g(b)+g(a).
$$
Each block weighs at least $g(b)$. Subtract that common constant from each block sum. The resulting nonnegative word still avoids additive squares because any such square would lift to the original word. Iterating with $a=b=62$ in the sense of repeated grouping yields $g(62^j)\ge73(62^j-1)/61$. Superadditivity (Fekete's lemma) and the finite upper bound below prove the claim about the limit.

For an explicit upper construction take the repeating 30-letter template
```
0 1 0 2 0 1 0 3 1 0 2 0 1 0 9 0 1 0 2 0 1 3 0 1 0 2 0 1 0 6
```
with weight 37. For each starting phase modulo 30 and each half-length 1 through 29 the two consecutive sums differ modulo 10. The companion Lean and C++ files check all 870 comparisons. The same conclusion holds for any half-length not divisible by 30 by subtracting full periods from both sums.

Define an infinite word on positive indices by using the template at every index $i$, then adding $10e_{i/30}$ if $30\mid i$. This defines $e_i$ recursively at smaller indices. An additive square of half-length not divisible by 30 is excluded modulo 10. At half-length $30h$ the template contributions agree, so equality forces equal sums in two adjacent length-$h$ blocks of the recursively sampled word. Repetition reduces to the excluded case. This word has nonnegative, unbounded letters.

Let $S(t)=\sum_{i=1}^t e_i$ and let $F_r$ be the weight of the first $r$ template positions. Then
$$
 S(30u+r)=37u+10 S(u)+F_r\quad(0\le r<30).
$$
Consequently $S(30^j)/30^j\to37/20$, which bounds $\gamma$. More quantitatively, for $\mu=37/20$, $D(t)=S(t)-\mu t$ satisfies $D(30u+r)=10D(u)+F_r-\mu r$. The finite prefixes obey $|F_r-\mu r|\le453/20$. Iteration over base-30 digits gives $|D(t)|\le(453/18)t^\theta$ for $t\ge1$, where $\theta=\log(10)/\log(30)$. Thus this word also provides noncoverable lists of span $qn+\mu q+O(q^\theta)$ whenever $n+\mu>4(453/18)q^\theta$. For unequal index gaps the affine term in the endpoint equation then dominates its error; equal index gaps are ruled out by avoidance. This joint range is a separate bound from the iterated limit in (1).

## Exact computation and relation to Erdős 142

The checker calculates $g(q)$ for every $1\le q\le62$. It tests budgets in increasing order from the best lower bound given by splits at shorter lengths. For two equal-length halves the bound increases by one because their weights must differ. For each budget a prefix search tries all nonnegative next letters consistent with the remaining certified minimum. Appending a letter only creates new forbidden blocks ending at that letter, all of which the checker tests. A surviving full word is an upper witness and a failed budget excludes every word within that budget. A separate implementation using prefix sums gave the same 62 minima. Run the standalone checker with a C++17 compiler; its columns are word length, exact minimum and largest conflicting lift for the returned witness. The Lean file checks the finite modular template and the dominance step in the lifting argument. The word minima are checked by exhaustive integer search in C++.

At $q=32$ the binary split alone gives $R(32n+31)\le32R(n)$. The verified padding 35 extends this by four sites and the geometric threshold in (1) is exact already for $n\ge8$. More generally if $R(n)=R(n-1)+1$ and $n\ge2$, then $R(qn+g(q)-q)\le q(R(n)-1)$ whenever the argument is positive. For large $q$ this gives padding linear in $q$ even after paying for the original jump. These are upper transfers between finite scales. The classical ratio-one asymptotic for $R(N)$ remains open.

The equal-index condition is the double arithmetic progression studied by [Brown, Jungić and Poelstra](https://arxiv.org/abs/1304.1829). A recent preprint on bounded alphabets is [Shallit, *An additive-square-free word over an alphabet of size 6*](https://arxiv.org/abs/2611.24441). Our upper construction uses an unbounded alphabet with controlled mean and is proved here independently. The preceding binary split is recorded in [ProgressionCovers.md](https://github.com/Deldor14/open-math-agents/blob/15f0f30b0989cb10be56ce7b40e68e1b9cde4c7c/research/erdos142-hinge/ProgressionCovers.md).
