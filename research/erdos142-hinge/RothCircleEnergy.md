# A circle integral for the deterministic Erdős 142 density

Let $R_k(N)$ be the greatest size of a subset of $[0,N)$ containing no nonconstant $k$-term arithmetic progression, $k\ge3$, and put $U(N)=N/R_k(N)$. On the circle with Haar probability define, for nonnegative $f\in L^k$ of integral one,
$$
 J(f)=\int f^k,\qquad L(f)=\int_{\mathbb T^2}\prod_{j=0}^{k-1} f(x+jd)\,dx\,dd,
 \qquad E_k(N)=\inf_f \{J(f)+N L(f)\}.
$$
The infimum uses one circle for every $N$. At every integer $N\ge1$,
$$
 E_k(N)\asymp_k U(N)^{k-1},\qquad
 \frac{16}{27}U(N)^2\le E_3(N)\le18 U(N)^2.                       \tag{1}
$$
The later [sharp finite rounding theorem](RothCubicRank.md) improves the lower coefficient in (1) to one, for every $N$ and in every uniformity. Its cubic interval minimum is verified in Lean.

In particular $\log(N/R_3(N))=\tfrac12\log E_3(N)+O(1)$. The uncertainty in the displayed logarithm from these explicit inequalities has width $\tfrac12\log(18\cdot27/16)$. A leading coefficient or exponent for the divergent logarithmic deficit transfers in both directions. The multiplicative error in (1) still matters for a ratio-one equivalent for $R_3(N)$.

For $B\ge1$, take the same infimum over periodic $W^{1,k}$ functions with $\|f'\|_k\le B\|f\|_k$ and call it $E_k(N,B)$. With $b=\min(N,\lfloor B\rfloor)$, the complete two-scale estimate is
$$
                  E_k(N,B)\asymp_k (1+N/b)U(b)^{k-1}.             \tag{2}
$$
Consequently a fixed-factor approximation to $E_k(N)$ needs relative derivative at least $cN$ and relative derivative $O_k(N)$ suffices. For Fourier polynomials any degree $o(N)$ loses an unbounded factor. Degree $O(N\log(2N))$ suffices for a fixed-factor approximation. The last section gives the resulting sextic minimization for three terms.

The arithmetic averaging follows the Varnavides method. Croot studied the minimum three-term progression density at a prescribed set density in large prime cyclic groups. Here the amplitude is unconstrained, the normalization is unit mass and the diagonal moment is penalized. We compare the resulting optimum with the interval rank at the specified integer length and quantify its change under a derivative restriction. [Croot and Sisask, Proposition 7.1](https://ecroot.math.gatech.edu/prob-almost-periods.pdf), [Croot on minimum progression density](https://arxiv.org/abs/math/0501004).

## Sampling and clipping

Write $a=a_{k,N}$ for the number of increasing nonconstant $k$-term progressions in $[0,N)$ and $c=(k-1)^{k-1}/k^k$. For $0\le g\le1$, choose uniform independent $x,d\in\mathbb T$. Retain the index $i$ with probability $g(x+id)$, independently conditional on $x,d$. Each index has mean $\int g$. An index progression of positive step $s$ has joint retention probability $L(g)$ because $(x,d)\mapsto(x+id,sd)$ preserves Haar probability. Delete a site from each surviving progression. This gives $\int g\le U(N)^{-1}+(a/N)L(g)$.

For arbitrary $f\ge0$ of mean $m>0$ apply this inequality with $g=\min(f/t,1)$. The elementary sharp clipping inequality $u\le\min(u,1)+cu^k$ follows by maximizing $(u-1)/u^k$ over $u\ge1$. Since $L(g)\le t^{-k}L(f)$, we get $t^{k-1}(m-t/U(N))\le cJ(f)+(a/N)L(f)$. Maximizing the left side at $t=(k-1)mU(N)/k$ gives
$$
           m^k U(N)^{k-1}\le J(f)+\frac{a}{Nc} L(f).                \tag{3}
$$
Here $J$ and $L$ also denote the same homogeneous expressions on unnormalized functions. Hölder and translation invariance bound $L(f)$ by $J(f)$. For $k=3$, $a=\lfloor(N-1)^2/4\rfloor\le N^2/4$ and $c=4/27$. This proves the lower bound in (1). For general $k$, $a\le N^2$ suffices.

## Arc witnesses and exact correlation

Take any nonempty free set $A\subset[0,N)$ of size $M$. At each $j/(2N)$, $j\in A$, start a half-open arc of width $w=1/(4N)$ on the circle. If an arithmetic progression lies in their union, write its coordinates as a center plus an error in $[0,w)$. The second difference of the errors has absolute value strictly below $2w=1/(2N)$. The second difference of the centers is a multiple of $1/(2N)$ and must therefore vanish modulo one. Its integer numerator has absolute value at most $2N-2$, so it vanishes in the integers. The index list is a constant or a nonconstant arithmetic progression, in either orientation. Freeness forces all terms into one arc.

For one arc, integrate first over the first two terms, which are independent uniform points. Their signed difference in real representatives must be the common difference of all consecutive representatives since all these differences lie in $(-w,w)$ and agree modulo one. The allowable region has area $w^2/(k-1)$, by parametrizing by the first and the last point with Jacobian $1/(k-1)$. Thus if $g$ is the union indicator, $\int g=Mw$ and $L(g)=Mw^2/(k-1)$ exactly. For $k=3$ the normalized function $f=g/(Mw)$ has $J(f)=16(N/M)^2$ and $NL(f)=2(N/M)^2$. Using an extremal $A$ proves the upper side of (1) for all $k$, with the stated three-term constant.

For derivative control replace every indicator by the triangular tent of height one on that arc, with slopes $\pm 2/w$. The mean becomes $Mw/2$, the $k$th moment becomes $Mw/(k+1)$ and the unnormalized correlation is at most $Mw^2/(k-1)$. Normalizing the mean keeps the relative derivative at $2(k+1)^{1/k}/w\le16N$. Thus both terms satisfy the required upper bounds at derivative budget $16N$.

## The cost of restricting translations

Let $f$ be admissible for the derivative budget $B$. Write $C_f(d)=\int\prod_j f(x+jd)\,dx$. Replacing the factors one at a time and applying Hölder gives, for $|d|\le1/2$,
$$
 |C_f(d)-J(f)|\le\|f\|_k^{k-1}\sum_{j=1}^{k-1}\|f(\cdot+jd)-f\|_k
 \le \tfrac12 k(k-1) B|d|J(f).
$$
Integration on $|d|\le1/(k(k-1)B)$ yields $J(f)\le k(k-1)B L(f)$. If $b=\lfloor B\rfloor\le N$, apply (3) at $b$, using $B< b+1\le2b$. This gives $b L(f)\gg_k U(b)^{k-1}$ and hence the lower bound in (2). If $B\ge N$, (1) applies directly.

For the reverse bound with $b\ge32$, use the tent construction at $m=\lfloor b/16\rfloor$. Its relative derivative is at most $B$. Its energy at parameter $N$ is $O_k((1+N/m)U(m)^{k-1})$. Partitioning $[0,b)$ into intervals of length at most $m$ gives $U(m)\le2U(b)$. For $b<32$ the constant function has energy $1+N$, within a fixed factor of the right side of (2).

To see the necessity of linear derivative scale, take $N/b=s\ge4$ and $a=\lfloor N/(2b)\rfloor$. Free sets of digits at lengths $a,b$ give a free set at length $N$ using radix $2b$. Indeed the second differences of the lower digits have absolute value less than $2b$, so both digit lists must be progressions and then constant. Thus $U(N)\le4 U(a)U(b)$. Since $a\le\lceil s\rceil$, partitioning gives $U(a)\le2U(\lceil s\rceil)$. The ratio in (2) to (1) is bounded below by
$$
    c_k\,s/U(\lceil s\rceil)^{k-1}
    \ \ge\ s\exp[-O_k((\log(2s))^{1/\lceil\log_2 k\rceil})].
$$
This diverges uniformly with $s$ by the [Rankin–O'Bryant construction](https://arxiv.org/abs/0811.3057).

A measurable translation conclusion holds even without differentiability. Suppose $J(f)+NL(f)\le K U(N)^{k-1}$ and $\int f=1$. Then $J(f)\gg_{k,K}U(N)^{k-1}$. To see this for all large $N$, fix a large integer $s$ depending only on $k,K$, and take $b=\lfloor N/s\rfloor$. Applying (1) at $b$ gives $J(f)\ge c_k U(b)^{k-1}-bL(f)$. The preceding digit argument with $N/b\le2s$ bounds the first term below by $c'_k U(N)^{k-1}/U(2s)^{k-1}$ (by partitioning at $2s$). The second term is at most $KU(N)^{k-1}/s$. The construction cited above permits $s$ large enough to absorb it. Bounded $N$ follow from $J(f)\ge1$.

Put $P_f=\{d:\|f(\cdot+d)-f\|_k\le\|f\|_k/[k(k-1)]\}$. Translation invariance and the triangle inequality bound each $j$-fold shift by $j$ times the single-shift difference. The same factor replacement gives $C_f(d)\ge J(f)/2$ throughout $P_f$. Hence its Haar measure is at most $2L(f)/J(f)\ll_{k,K}1/N$. The order is attained by the tent witnesses, since their derivative bound puts an interval of that length into $P_f$.

## Accuracy near the infimum

There is a stronger obstruction for high accuracy. Allow positive real penalties in the definition of $E_k$. Set $v_j=\log E_k(2^{j+1})-\log E_k(2^{j-1})$. The infimum is nondecreasing and positive. Summing the nonnegative variations through $j=J$ telescopes to $O_k((1+J)^\beta)$ by (1) and the Rankin lower construction, where $\beta=1/\lceil\log_2 k\rceil$. Fix any nondecreasing $\omega(j)\to\infty$. Except on a set of indices of density zero we have $v_j\le \omega(j)j^{\beta-1}$. Indeed, on $H\le j<2H$ Markov's inequality discards $O_k(H/\omega(H))$ indices; summing dyadic blocks preserves zero density.

For $2^j\le N<2^{j+1}$ take any unit-mass competitor with $J(f)+NL(f)\le(1+\epsilon)E_k(N)$. The same competitor in the infimum with penalty $N/2$ gives
$$
 NL(f)\le 2[(1+\epsilon)E_k(N)-E_k(N/2)]
        \le 2(\epsilon+v_j)E_k(N).
$$
Here $1-e^{-v_j}\le v_j$. Whenever $\epsilon+v_j\le1/4$, it follows that $J(f)\ge E_k(N)/2$. For all such competitors, $|P_f|\ll (\epsilon+v_j)/N$. The local translation estimate then implies $\|f'\|_k/\|f\|_k\gg_k N/(\epsilon+v_j)$ when a derivative exists: apply that estimate with $B=\max(1,\|f'\|_k/\|f\|_k)$; for large $N$ the bound forces $B>1$. By Bernstein the same lower bound holds, up to constants, for the degree of a polynomial competitor.

In particular, for three terms and relative error at most $1/\log N$, a polynomial attaining that accuracy needs degree at least $cN\sqrt{\log N}/\log\log N$ on a set of integer lengths of logarithmic density one. Use $\omega(j)=\log(2+j)$; a density-zero set of dyadic indices corresponds to a set of lengths of logarithmic density zero. For errors tending arbitrarily slowly to zero, degree divided by $N$ still tends to infinity along a common set of lengths of logarithmic density one (for example with this same $\omega$). This statement concerns accuracy relative to the variational infimum; (1) retains its explicit constants.

## Finite Fourier optimization

Bernstein's inequality $\|f'\|_k\le2\pi D\|f\|_k$ for trigonometric polynomials of degree $D$ and (2) give the degree obstruction. We give an upper construction of degree $O(N\log(2N))$. In the same center positions use narrower arcs of width $1/(16N)$. Convolve their union indicator with the nonnegative kernel proportional to
$$
       \left|m^{-1}\sum_{j=0}^{m-1}e^{2\pi i jx}\right|^{2h},
       \qquad m=64N,\quad h=10\lceil\log_2(2m)\rceil .
$$
For $\|x\|\ge1/(32N)$ the normalized sum has magnitude at most $1/(2m\|x\|)\le1/4$. For $\|x\|\le1/(4m)$ it is at least $2/\pi\ge1/2$ by the sine formula. The normalized kernel has mass at most $2m\,4^{-h}\le N^{-2}$ outside the first neighborhood. The convolved function $g$ stays in $[0,1]$, has mean $M/(16N)$ and is at most $N^{-2}$ outside the enlarged arcs of width $1/(8N)$. These enlarged arcs have the same guard as above, since they are a common translate of arcs that start at the centers. Thus $L(g)\le M/(64(k-1)N^2)+N^{-2}$ and $J(g)\le\int g$. Normalization proves the asserted upper energy bound. Its degree is at most $D=h(m-1)$.

For $k=3$, Fejér–Riesz factorization writes a nonnegative unit-mean polynomial of degree at most $D$ as $|\sum_{j=0}^D z_j e^{2\pi ijx}|^2$ with $\sum |z_j|^2=1$. Set $a_h=\sum_j z_{j+h}\overline{z_j}$ with coefficients outside $[0,D]$ taken as zero. The restricted optimum is exactly the minimum on this unit sphere of
$$
    \sum_{u+v+w=0} a_u a_v a_w+N\sum_t a_t^2 a_{-2t}.
$$
These real-valued expressions follow by integrating the constant terms in one and two variables respectively. The explicit cutoff above recovers $\log(N/R_3(N))$ to a bounded additive error. Determining its growth still requires a quantitative bound on this minimum. [Bernstein inequality](https://www.sciencedirect.com/science/article/pii/S0021904522000090), [Fejér–Riesz factorization](https://uva.theopenscholar.com/files/james-rovnyak/files/p71.pdf).

## Verification

[Seven Lean lemmas](RothCircleEnergy.lean) certify deletion of active edges, its weighted average for an arbitrary finite sample law, the sharp cubic clipping cost, the optimization in (3) for $k=3$, and the integrated cubic inequality under its clipped-sampling hypothesis, the finite period count and the two-scale loss estimate. The circle integration, Sobolev estimates and their asymptotic consequences have written proofs. [An independent exact verifier](check_roth_circle_energy.py) checks 16,605 weighted cyclic inequalities, 1,123 continuous arc integrals by rational polygon dissection, and 624 Fourier identities.
