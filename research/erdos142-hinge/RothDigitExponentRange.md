# Upper and lower density exponents for all fixed progression lengths

For $k\ge3$ let $r_k(n)$ be the largest cardinality of a subset of $[0,n)$ with no nonconstant $k$-term arithmetic progression. The density deficit at dimension $t$ is $D_t=\log(2^t/r_k(2^t))$. Let $\beta_-$ and $\beta_+$ be the liminf and limsup of $\log(1+D_t)/\log t$. They lie in $[0,1/2]$ since every three-term-free set is also $k$-term-free and Behrend gives $D_t\le4\sqrt{t\log2}$. All logarithms are natural. [Behrend bound](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Additive/AP/Three/Behrend.html)

Fix $1/2\le\theta<1$ and $0<\eta\le1$. In dimension $d\ge2$ take every nonempty $k$-term-free $A\subset[0,2^d)$ satisfying $D_A=\log(2^d/|A|)\le10d^\theta$. For its uniform random point, sort the mutual informations between the bottom $j$ bits and the remaining bits, $1\le j<d$. Let $J(d)$ be the minimum over these sets of the $\lceil\eta(d-1)\rceil$-th smallest value. The eligible collection is nonempty by Behrend. Then
$$\boxed{\displaystyle
\liminf_{d\to\infty}\frac{\log(1+J(d))}{\log d}
=\frac{(1-\theta)\beta_-}{1-\beta_-},\qquad
\limsup_{d\to\infty}\frac{\log(1+J(d))}{\log d}
=\frac{(1-\theta)\beta_+}{1-\beta_+}.} \tag{1}$$
In particular, existence of the density exponent for $r_k$ is equivalent to existence of the digit-information exponent for any one fixed admissible pair $(\theta,\eta)$. If its measured value is $s$, the density exponent is $s/(1-\theta+s)$. The result characterizes power exponents of the deficit. The requested asymptotic equivalent for $r_k(n)$ remains open. [Erdős problem 142](https://www.erdosproblems.com/latex/142)

## Finite input

For any sequence of cuts, let $\ell_i$ be the lengths of the consecutive blocks they delimit. The argument using conditional block entropies in the companion gives
$$\sum_{j\text{ chosen}} I_j(A)\ge\sum_i D_{\ell_i}-D_A. \tag{2}$$
After fixing all other blocks, a block of $s$ bits sits in an affine progression in the original interval. Any nonconstant $k$-term progression in the possible digit values would map to one in $A$. This proves the conditional capacity bound for every $k$. The Lean theorem uses the upstream definition of $r_k$ on $[1,n]$, with the unit translation included in the proof. [Finite multicut theorem in Lean](RothLongDigitInformation.lean) · [Three-term information proof](RothDigitInformation.md)

If $b$ cuts have $I_j\le h$, choose a residue class modulo $t$ containing $q\ge b/t$ of them. The $q-1$ interior gaps have length at least $t$. Splitting a dyadic interval into translates of a smaller one shows $D_s\ge D_t$ for $s\ge t$. Consequently
$$(q-1)D_t\le D_A+qh.\tag{3}$$
For $q\ge2$, the extraction in the companion actually produces a $k$-term-free set with deficit at most $(D_A+qh)/(q-1)$ on a $t$-bit interval.

Conversely, for any $1\le t\le d$, write $d=m(t+1)+r$ with $0\le r\le t$. Use an optimal $t$-bit seed in each of $m$ blocks, with a fixed zero as the most significant bit of each block. When $r>0$, use an optimal $(r-1)$-bit seed and a fixed zero bit in the final block. The zero-bit seed has one value. With $g=D_t+\log2$, the Cartesian product encoded by these digits has
$$D_A\le(m+1)g,\qquad \max_{1\le j<d}I_j(A)\le D_t.\tag{4}$$
The total deficit adds across independent blocks and the final seed deficit is at most $D_t$. Each cut shares at most one seed between its two sides. The full seeds on either side are independent, while the two parts of a split seed have total marginal entropy at most its width times $\log2$. Subtracting the joint entropy gives the information bound.

To check progression avoidance for $k>3$, consider the equations $x_i+x_{i+2}=2x_{i+1}$ of a putative progression. In the lowest block both sides of each digit sum are below the radix. Reduction therefore gives an ordinary midpoint equation for every triple of successive digits. The sequence of $k$ low digits is an arithmetic progression in the integers, possibly decreasing; the seed forces it to be constant. Remove that common digit, divide by the radix and repeat. All original points were equal. This argument allows nonconstant triples in a $k$-term-free seed when $k>3$. Lean verifies the cardinality, the midpoint argument in both directions, and progression avoidance for two arbitrary finite seeds. [Guarded products](RothGuardedDigits.lean)

## Passing to exponents

Write $F_\theta(x)=(1-\theta)x/(1-x)$. First suppose that $J(d)\le d^\gamma$ along a sequence tending to infinity, where $0<\gamma<\theta$. Set $t=\lfloor d^{1-\theta+\gamma}\rfloor$ and apply (3) to a minimizing set and all cuts up to the indicated quantile. Since $q\ge\eta(d-1)/t\to\infty$, the bound gives $D_t=O_\eta(d^\gamma)$. This proves $\beta_-\le\gamma/(1-\theta+\gamma)$. If $J(d)\le d^\gamma$ at every sufficiently large $d$, the same comparison gives this bound for $\beta_+$: the floor of $d^{1-\theta+\gamma}$ takes every sufficiently large integer value because its consecutive increments before rounding tend to zero. For either liminf or limsup, a putative value strictly below $F_\theta(\beta_\pm)$ admits a strictly intermediate positive $\gamma<\theta$, since $0\le F_\theta(\beta_\pm)\le 1-\theta\le\theta$. This proves both lower bounds, including the zero endpoints.

For the reverse liminf take $t$ on a sequence attaining $\beta_-$, and use
$$m=\max\left(1,\left\lfloor(t^\theta/g)^{1/(1-\theta)}\right\rfloor\right),\qquad d=m(t+1).$$
Here the product has deficit exactly $mg$. When $m\ge2$ the choice gives $mg\le(mt)^\theta$; otherwise $g\le5\sqrt t\le5d^\theta$. All cuts have information at most $D_t$. Because $g\le5\sqrt t$ and $\theta\ge1/2$, the expression inside the floor is bounded below by a positive constant depending only on $\theta$. Thus the maximum and floor affect its logarithm by $O_\theta(1)$, giving $\log d/\log t\to (1-\beta_-)/(1-\theta)$. This yields the desired upper bound for the liminf.

For the reverse limsup, if $\beta_+<\theta$, choose $v$ strictly between them. Eventually $g\le t^v$. In each sufficiently large dimension set $t=\lceil d^{(1-\theta)/(1-v)}\rceil\le d$. By (4),
$$D_A\le(d/t+1)g\le d^\theta+t^v\le 10d^\theta$$
for large $d$, since $v(1-\theta)/(1-v)<\theta$. This gives $\limsup\log(1+J(d))/\log d\le F_\theta(v)$. Let $v$ decrease to $\beta_+$. The remaining endpoint is $\beta_+=\theta=1/2$. Directly take an optimal $d$-bit seed; $I_j\le D_d\le4\sqrt{d\log2}$ for all cuts, which gives the upper bound $1/2$.

## Smaller cutoffs for longer progressions

Write $h=\lceil\log_2 k\rceil$. O’Bryant’s lower bound on $r_k(2^t)$ gives
$$D_t\le C_h t^{1/h}-\frac{\log t}{2h}+O_k(1),\qquad C_h=(\log2)h2^{(h-1)/2}.$$
Consequently (1) with the original cutoff $10d^\theta$ holds for every $1/h<\theta<1$. It also holds at $\theta=1/h$ with that cutoff when $3\le k\le16$; for any fixed $k$ it holds at the boundary with cutoff $C d^\theta$ for $C>\max(1,C_h)$. Indeed the comparison uses $\beta_+\le\theta$, $g=O(t^\theta)$ and eventual eligibility of an optimal seed at the selected coefficient. These replace the square-root bounds word for word: $F_\theta(\beta_+)\le\theta$, and when $\beta_+=\theta$ the single optimal seed gives the upper endpoint directly. Only sufficiently large dimensions enter the limits. The verifier chat supplied this extension and kernel proofs for logarithmic subsequence comparisons, the integer guarded-product scaling, and the exact right inverse needed for floor powers. [O’Bryant, Theorem 1](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v18i1p59) · [Seven scale lemmas in Lean](RothDigitLogTransfer.lean)

## A finite three-term consequence

For $k=3$, $\theta=1/2$ and fixed $\eta>0$ the bound is
$$J(d)\gg_\eta \frac{d^{1/10}}{(\log d)^{6/5}}.$$
Indeed, if $t\le d$, $0<D_t\le5\sqrt d$ and $128t\le\eta D_t\sqrt d$, (3) with $h=D_t/2$ bounds the number of cuts at information at most $D_t/2$ by $2t(10\sqrt d+D_t)/D_t<\eta(d-1)$. The inequality follows by choosing $t=\lfloor(c_\eta\sqrt d/\log d)^{6/5}\rfloor$ with $c_\eta>0$ sufficiently small, since $D_t\gg t^{1/6}/\log(2t)$. In the opposite finite comparison, $g\sqrt d\le t$ and $g\le5\sqrt d$ give a product of deficit at most $6\sqrt d$ by (4). [Raghavan, Theorem 1.1](https://arxiv.org/abs/2603.27045v3) · [Finite numerical comparisons in Lean](RothDigitScaleComparison.lean)

## Verification and contributions

The finite multicut theorem for the upstream extremal number, the arbitrary two-seed product, and the two numerical scale comparisons have kernel-checked Lean proofs. The quantile limits, the information estimate for products and the application of Raghavan's bound are written proofs. The structural-estimates chat developed the multicut method and characterization. The scalar-model chat independently checked the original inverse and proposed varying the cutoff exponent. The verification and transference chat independently checked both directions in the square-root case, including the incomplete final digit, the limsup comparison and the endpoint estimate; it contributed the two numerical Lean lemmas and the incomplete-product verifier. An additional exhaustive program checks (2) for lengths of progression 4, 5 and 6 at ambient length 16, as well as exact cut information on mixed products of several kinds of seeds. [General finite verifier](check_roth_long_digits.py) · [Independent incomplete-product verifier](check_roth_incomplete_digits.py)
