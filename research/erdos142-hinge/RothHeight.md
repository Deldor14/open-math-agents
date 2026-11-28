# The Roth density deficit and the width of graphs avoiding three-term progressions

Let $R(N)=r_3(N)$ and $d(N)=\log(N/R(N))$, with natural logarithms. A graph on the integer index set $0,\ldots,N-1$ is progression-free if $f(i)+f(k)\ne2f(j)$ whenever $i<j<k$ and $i+k=2j$. Its heights are integers.

For a word of $N-1$ positive integers write $P_0=0$ and $P_i$ for its prefix sums. Avoiding adjacent blocks of equal length and equal sum is equivalent to the graph of $P_i$ being progression-free. Let $W_N$ be the minimum possible oscillation of $P_i-si$ over these indices, over all real $s$ and all such words. Subtracting or adding an integer multiple of $i$ does not affect this optimization. In particular the positivity of the letters imposes no additional restriction on a finite graph after allowing a slope.

We establish the following three comparisons.

1. $\log(1+W_N)=d(N)+O(\sqrt{d(N)})$ as $N\to\infty$.
2. There is a single integer-valued progression-free graph on all nonnegative indices whose maximum height below $N$ has logarithm $d(N)+O(\sqrt{d(N)})$. Heights may decrease between consecutive indices.
3. There is a single infinite **positive integer word** avoiding additive squares, of finite mean $\mu$, whose prefix discrepancy $E(N)=\max_{0\le i<N}|P_i-\mu i|$ satisfies
$$
 d(N)-O(1)\le\log(2+E(N))\le4d(N)+O(\sqrt{d(N)}).
$$
The prefix estimate is not a bound on deviations over all starting indices. Letters need not be bounded. The comparisons transfer estimates for the original $R(N)$; none currently gives a ratio-one asymptotic for $R(N)$.

## Finite strips and cyclic height templates

If the residuals $P_i-si$ span an interval of length $W$, put them into $\lfloor2W\rfloor+1$ half-open bins of width $1/2$, starting at the minimum. A progression of indices from one bin would have integral vertical second difference of absolute value strictly less than 1, hence zero. Each bin contains at most $R(N)$ indices. Thus
$$
 2W+1\ge N/R(N). \tag{1}
$$

Conversely, for each $L\ge3$ there is a map $h_L:\mathbb Z/L\to\{0,\ldots,m_L-1\}$ such that
$$
 h_L(a)+h_L(a+2t)\not\equiv2h_L(a+t)\pmod {m_L}
 \quad(t\not\equiv0\pmod L),\qquad
 \log m_L\le d(L)+O(1+\sqrt{d(L)}). \tag{2}
$$
Take an optimal set on $\ell=\lfloor L/2\rfloor$ points and embed it in $\mathbb Z/L$. Every modular progression inside this interval is an ordinary one since every lifted second difference has absolute value less than $L$. This also excludes a nonzero step of order two. Independent random translates cover the whole group with at most $c=\lceil(L/R(\ell))(1+\log L)\rceil$ translates: the expected number left uncovered is less than 1. Assign each point to one covering translate. Monochromatic index progressions of nonzero step are now impossible.

Choose $K$ with $R(K)\ge c$ and give the colors distinct labels from a progression-free set in $[0,K)$. Take $m_L=2K+1$. Any zero modular second difference of labels is an ordinary zero and forces all labels to coincide. This gives (2)'s avoidance assertion. For size, $R(L)\le\lceil L/\ell\rceil R(\ell)$ implies $\log c\le d(L)+O(1+\log\log L)$. The Behrend lower bound gives $K\le c\exp(C\sqrt{\log(2c)})$ for an absolute $C$, by applying it at an integer of that size with $C$ sufficiently large. The Bloom–Sisask upper bound gives $d(L)\gg(\log L)^{1/9}$, so $\log\log L=o(\sqrt{d(L)})$. This proves (2). The ordinary graph $h_N$ gives $W_N\le m_N$ after adding a sufficiently steep integer line. Together with (1) this proves the first assertion.

**Exact small cases.** The rational verifier gives $W_2=0$, $W_3=W_4=1/2$, $W_5=\cdots=W_8=1$, $W_9=\cdots=W_{12}=3/2$, and
$$
 (W_{13},W_{14},W_{15},W_{16})=(7/4,11/6,13/7,2).
$$
Run `python3 height_strip_search.py 16` to reproduce the values and witnesses. The independent checker `python3 height_strip_fixed.py` enumerates slopes and intercepts first and verifies feasibility at each reported width and infeasibility at its immediately preceding candidate width. Fix the initial height at zero and normalize the slope to $[0,1/2]$ by integer shears and sign reversal. Each new height must meet the slope bounds from every earlier height and must not complete an index progression with zero vertical second difference. The verifier enumerates every candidate meeting these necessary constraints. For a fixed graph the width as a function of slope is piecewise affine; the pieces change only when two residuals tie. Thus an optimum slope is 0, $1/2$, or a rational of denominator at most $N-1$. At that slope the width has the same denominator bound (allowing denominator 2 for the endpoints). An initial finite feasible width bounds all normalized heights in the search, so the minimum is attained.

## One graph at every scale

At dyadic lengths $d(2^j)$ is nondecreasing, unbounded, and its increments are at most $\log 2$. Fix $a=4$. Let $T_j$ be the first dyadic length at which $d$ reaches $aj$. Use the template for $T_{j+1}$ on the index interval $[T_j,T_{j+1})$; handle $[0,T_1)$ as one initial band. Shift all heights in band $j$ by $3\max(B_{j-1},m_{T_{j+1}})$, where $B_{j-1}$ is the largest height so far (start with 1). Any progression of heights using different bands is impossible. In the largest occupied band all heights lie between $3K$ and $4K$ and all earlier heights are at most $K$, with the top of the current band strictly below $4K$. Whether one or two of the three heights are in the largest band, the midpoint equation fails. Three indices in one band are covered by its template.

The new maximum is at most $4\max(B_{j-1},m_{T_{j+1}})$. Iteration and (2) give $\log B_j\le a(j+1)+O(\sqrt{j+1})$ because $a>\log 4$. For any $1\le u\le v$, partitioning $[v]$ into $u$-point intervals gives $d(v)\ge d(u)-\log2$. Thus throughout a band $d(N)\ge aj-\log2$. This proves the upper estimate for the single graph. The level sets themselves are progression-free, so the logarithm of one plus its maximum height is at least $d(N)$.

## One positive word with a fixed mean

Choose a sufficiently large dyadic $B_1=L_1$ with $d(B_1)>0$, and put $B_0=M_0=1$. For $j\ge2$ choose $L_j$ to be the first dyadic length with $d(L_j)\ge 2d(B_{j-1})$ and put $B_j=B_{j-1}L_j$. Write $m_j=m_{L_j}$ from (2), $M_j=\prod_{i\le j}m_i$. We have $L_j\ge B_{j-1}$, $d(L_j)\le2d(B_{j-1})+\log2$, and $d(B_j)\ge d(L_j)$ by dyadic monotonicity. Geometric summation in (2) gives
$$
 \log M_j\le 4d(B_{j-1})+O(1+\sqrt{d(B_{j-1})}). \tag{3}
$$

Extend $h_j=h_{L_j}$ periodically to the integers. Take the positive periodic letters $p_j(t)=m_j+h_j(t)-h_j(t-1)$. Define the actual infinite word on $n\ge1$ by the finite sum
$$
 e_n=\sum_{j:B_{j-1}\mid n}M_{j-1}p_j(n/B_{j-1}).
$$
Modulo $m_1$ a putative additive square must have half-length divisible by $L_1$, by (2). Then the first-layer contributions are equal, the higher contributions are multiples of $m_1$, and each half contains the same number of consecutive multiples of $L_1$. Division by $m_1$ gives an additive square in the tail construction on adjacent blocks with new half-length equal to the original half-length divided by $L_1$. Iteration is impossible for a positive finite half-length. This proves avoidance at every starting position.

Put $\mu=\sum_{j\ge1} M_j/B_{j-1}$. This is finite. Indeed the ratio of successive terms is $m_{j+1}/L_j$, which tends to zero since $\log m_{j+1}=O(\sqrt{\log B_j})$ by (2), (3) and Behrend, whereas $\log L_j\ge\tfrac12\log B_j$ for $j\ge2$. For $B_{j-1}\le n<B_j$, summing a full layer up to $n$ telescopes its heights at $z=\lfloor n/B_{i-1}\rfloor$. Its contribution is $M_{i-1}(m_i z+h_i(z)-h_i(0))$. Each active layer differs from its linear mean contribution by at most $2M_i$. The inactive tail has total mean contribution bounded by $2nM_{j+1}/B_j$ for all large $j$. Therefore
$$
 |P_n-\mu n|\le 4M_j+2(n/B_j)M_{j+1}. \tag{4}
$$

To bound the last term uniformly within large bands, note the following elementary scale inequality for $b\ge n$:
$$
 d(b)\le d(n)+O(1+\sqrt{\log(b/n)}). \tag{5}
$$
If $b<4n$, monotonicity of $R$ suffices. Otherwise take $s=\lfloor b/(2n)\rfloor$ and use $R(b)\ge R(n)R(s)$ from the digit bound in [RothExtensions.md](RothExtensions.md), followed by Behrend at $s$. With $t=\log(B_j/n)$, formulas (3) and (5) give
$$
 \log\bigl((n/B_j)M_{j+1}\bigr)
 \le4d(n)+O(1+\sqrt{d(n)})-t+O(\sqrt t+t^{1/4}).
$$
The terms depending only on $t$ are bounded above uniformly. Also $d(B_{j-1})\le d(n)+\log2$. This proves from (4) that $|P_n-\mu n|\le\exp(4d(n)+O(1+\sqrt{d(n)}))$. The same inequality for earlier indices and $d(i)\le d(N)+\log2$ handles the maximum in $E(N)$. Behrend implies $d(n)=O(\sqrt{\log n})$, giving $P_n/n\to\mu$. Since oscillation is at most twice the maximum absolute deviation, (1) yields the reverse bound $(4E(N)+1)R(N)\ge N$.

In particular, for every fixed $0<\alpha<1$, a bound $R(N)\ge N\exp(-O((\log N)^\alpha))$ for all large $N$ is equivalent to the existence of a single infinite positive word avoiding additive squares with finite mean and prefix discrepancy at most $\exp(O((\log N)^\alpha))$. This equivalence preserves the power in the logarithm and does not assert equality of the constants in its exponent.

Quantitative external inputs are the [Behrend-type lower bound](https://arxiv.org/abs/2406.12290) and the [Bloom–Sisask upper bound](https://arxiv.org/abs/2309.02353). The qualitative connections between additive sums and slopes have been studied by [Banero](https://arxiv.org/abs/1209.4691). For bounded-alphabet avoidance, see also the recent [Shallit preprint](https://arxiv.org/abs/2611.24441). The positive-word construction above permits arbitrarily large letters and is independent of the bounded-alphabet result.
