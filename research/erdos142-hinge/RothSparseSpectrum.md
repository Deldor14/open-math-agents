# How many Fourier modes can resolve the three-term progression energy?

On the circle let $J(f)=\int f^3$, $L(f)=\iint f(x-d)f(x)f(x+d)\,dx\,dd$, and let $E(N)$ be the infimum of $J+NL$ over $f\ge0$ of unit mean. Write $U(N)=N/r_3(N)$. A polynomial within any fixed factor $K$ of $E(N)$ needs at least $c_K N^{6/11}$ distinct Fourier modes, even when their positions are arbitrary integers. Every polynomial $P$ representing that profile as $f=|P|^2$ separately needs at least that many modes. With the more recent restricted sum–difference bound, the exponent in both statements is $114631769327023765/209357544569848128=0.5475406657\ldots$.

We prove two inequalities that imply the result. Let $\alpha$ be any exponent for which the number of distinct restricted differences $c-a$ in a finite bipartite graph is at most $s^\alpha$ whenever the two vertex projections and the restricted sums $a+c$ each have at most $s$ values. Katz and Tao established $\alpha=11/6$. The exact rational exponent used for the second assertion is from Farnamfar's 2026 preprint. [Katz and Tao](https://arxiv.org/abs/math/9906097), [Tomar's intermediate bound](https://www.mefyi.com/papers/sum-difference-exponents/), [Farnamfar, Theorem 1](https://arxiv.org/abs/2611.19594).

* If a nonnegative trigonometric polynomial $f$ has $s$ modes, then $J(f)\le s^\alpha L(f)$.
* If $P$ is a complex trigonometric polynomial with $s$ modes, then $J(|P|^2)\le s^\alpha L(|P|^2)$.

Our parallel scalar research chat suggested bounding the correlation at step zero by its mean times the size of its frequency support. Averaging over the center frequency imposes the restricted-sum condition in the first proof below. The second proof controls each row before taking a squared norm. It applies to each actual representation, irrespective of the size of the spectrum of its square.

## The correlation of a nonnegative function

Let $S=\operatorname{supp}\widehat f$. Define $C(d)=\int f(x-d)f(x)f(x+d)\,dx$. A product of modes $a,b,c$ survives integration exactly when $a+b+c=0$, leaving step frequency $c-a$. Consequently the support of $\widehat C$ lies in
$$
 T_0(S)=\{c-a:a,c\in S,\ -a-c\in S\}.
$$
The two endpoint projections are contained in $S$, and their sums in $-S$. Hence $|T_0(S)|\le s^\alpha$. Since $C(d)\ge0$, every coefficient of $C$ has magnitude at most its mean $L(f)$. Summing them at zero proves the first inequality.

There is a tail form for any finite set $S$, including when $S$ omits some modes. Write $a_h=\widehat f(h)$. The coefficients on $T_0(S)$ still have magnitude at most $L(f)$. Each triple producing any other difference uses a mode outside $S$. For a fixed omitted frequency, the sum of the absolute products of the other two factors with prescribed sum is at most $\|f\|_2^2$ by Cauchy–Schwarz. Thus
$$
 J(f)\le |T_0(S)|L(f)+3\|f\|_2^2\sum_{h\notin S}|a_h|.            \tag{1}
$$
This argument also works for nonnegative functions with absolutely summable Fourier series.

## Restriction of products to the diagonal

For finite integer sets $A,B,C$ let $T_u(A,B,C)=\{c-a:a\in A,b\in B,c\in C,\ a+b+c=u\}$. Any polynomial $H(x,d)$ with Fourier support contained in
$$
    \{(a+b+c,c-a):a\in A,\ b\in B,\ c\in C\}
$$
satisfies
$$
 \int |H(x,0)|^2\,dx\le \max_u |T_u(A,B,C)|\,\iint |H(x,d)|^2\,dx\,dd.   \tag{2}
$$
Indeed each row with coefficients $z_{u,t}$ contributes $|\sum_t z_{u,t}|^2$ on the left and $\sum_t|z_{u,t}|^2$ on the right by Parseval. The best constant equals the stated maximum: take coefficients one throughout a maximizing row and zero elsewhere. For each row, the endpoint graph has its sums in $u-B$, so the restriction constant is at most $\max(|A|,|B|,|C|)^\alpha$.

Taking $H(x,d)=P(x-d)P(x)P(x+d)$ proves the second inequality. Fejér–Riesz guarantees a polynomial square factor for a nonnegative polynomial on the circle. Its frequency spacing and cardinality can differ from those of a chosen difference-set presentation of the square. The argument here uses the frequencies of the factor itself.

In fact the optimal *exponent* for (2) on all such linear spaces with $A=B=C=S$ is exactly the restricted sum–difference exponent. Given any graph with projections and sums of sizes at most $m$, put all its endpoints and all its negated sums into $S$, of size at most $3m$. The original restricted differences belong to $T_0(S,S,S)$. An exponent bound for (2) gives the restricted-difference bound with a constant, and conversely. Fixed constants can be removed by taking Cartesian powers and encoding coordinates by a sufficiently large integer radix, preserving the finitely many sums and differences without collisions. The same finite radix argument takes a graph over the reals into the integers after choosing a basis for the finitely generated additive subgroup of its coordinates. Sharpness in this paragraph is for the full linear space. The optimal exponent for the single product $P(x-d)P(x)P(x+d)$ is a separate question. For example $P=1+e^{2\pi ix}$ has $J(|P|^2)/L(|P|^2)=20/8$; products in separated frequencies give the lower exponent $\log_2(5/2)$ for that question. For this example the numerator and denominator multiply exactly by integrating the finite Fourier expressions without radix collisions.

## Consequences at the deterministic Erdős scale

By the [circle energy comparison](RothCircleEnergy.md), $E(n)\asymp U(n)^2$. Moreover $J(f)\gg_K U(N)^2$ for each unit-mean competitor with $J(f)+NL(f)\le K E(N)$. Thus $J/L\gg_K N$, and both cardinality bounds follow. Formula (1) gives a robust version: when $s^\alpha\le c_K N$, the omitted Fourier coefficients have total absolute mass at least $c'_K U(N)$, using $\|f\|_2^2\le\sqrt{J(f)}$ by interpolation with unit mass. In particular the same lower bound holds for the Fourier-algebra distance to every polynomial supported on those $s$ modes.

Without any near-optimality hypothesis, let $b=\max(1,\lfloor s^\alpha\rfloor)$. Either sparsity inequality and $E(b)\gg U(b)^2$ yield $L(f)\gg U(b)^2/b$ for a unit-mean polynomial with the specified frequency budget, whether imposed on $f$ or on a square factor. At high precision there is also a typical-length strengthening: for relative error at most $1/\log N$, the circle energy comparison gives $J/L\gg N\sqrt{\log N}/\log\log N$ on lengths of logarithmic density one. Either Fourier cardinality must be at least a fixed multiple of this quantity to the power $1/\alpha$. The large-scale growth of $U$ remains to be determined.

[The Lean source](RothSparseSpectrum.lean) proves the integer row identity, embedding of an arbitrary restricted-difference graph, the rowwise norm bound and its equality case, Parseval on finite circle spectra, restriction in the circle L² norm, and the coefficient-tail estimate. [The independent exact checks](check_roth_sparse_spectrum.py) expand both energies in two ways on 568 signed spectra and check the inverse graph construction for all 512 graphs on the selected sets.
