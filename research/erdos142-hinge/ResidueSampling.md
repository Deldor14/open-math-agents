# The optimal worst-pair loss in residue-class sampling

This note determines a limitation of the residue-class argument in [the counting note](RothEntropy.md). Fix $n\ge2$ and $D\ge1$. If a sampler chooses a modulus $d\in[D]$ with law $\mu$, two distinct sites at distance $a<n$ fall in the same residue class exactly when $d\mid a$. Let
$$
 K(n,D)=\inf_\mu\ \max_{1\le a<n}\sum_{d\mid a,\ d\le D}\mu(d).
$$
This optimizes over all moduli, including composites. Write $L=\log(n-1)$. For any fixed $B>1$, as $n\to\infty$, uniformly for $2\le D\le L^B$,
$$
 K(n,D)=(1+o_B(1))\min(1,L/D). \tag{1}
$$
In particular reducing the worst-pair coefficient to $o(1)$ requires $D/\log n\to\infty$. In the polylogarithmic range, giving each prime modulus weight proportional to its logarithm is asymptotically optimal even among all composite-modulus mixtures. This conclusion applies to an argument that bounds each cover edge by its worst pair difference. It leaves open the use of information about the joint distribution of differences in actual progression covers.

## Upper bound and the exact threshold

A prime law with weights $(\log p)/\vartheta(D)$, where $\vartheta(D)=\sum_{p\le D}\log p$, gives $K\le\min(1,L/\vartheta(D))$, since the product of distinct prime divisors of $a$ divides $a$. In fact $K(n,D)=1$ exactly when $\operatorname{lcm}(1,\ldots,D)\le n-1$. If this least common multiple fits, take it for $a$. Otherwise even the uniform law on all $d\le D$ has maximum at most $1-1/D$. The prime number theorem gives $\vartheta(D)\sim D$, $\log\operatorname{lcm}(1,\ldots,D)\sim D$, and $\pi(D)\sim D/\log D$. These estimates give the upper bound and settle (1) for $D\le L/2$, including bounded $D$. [Rosser and Schoenfeld, prime-function estimates](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf)

At finite sizes composites can strictly help. For $n=60,D=6$, the uniform law on $3,4,5$ gives an upper bound $2/3$, since their least common multiple is 60. A uniform random difference in $\{12,20,30\}$ is divisible by each of $1,\ldots,6$ with probability at least $2/3$, giving the matching lower bound. Every prime-only law on $2,3,5$ has cost one, witnessed by the difference 30.

## A random common difference for the lower bound

It remains to treat $L/2<D\le L^B$. We construct a random integer $1\le A\le n-1$ such that, for **each** $d\le D$, $\mathbb P(d\mid A)\ge(1-o_B(1))r$, where $r=\min(1,L/D)$. Averaging against any $\mu$ then proves the lower bound in (1). Put
$$
 Y=L^{1/3},\qquad \sigma=\max(0,1-\log L/\log D),
 \qquad \gamma=L^{-1/(10B)}.
$$
Here $0\le\sigma\le1-1/B$ and $D^{-\sigma}=r$. Use three disjoint prime ranges.

* For $p\le Y$ include all powers of $p$ up to $D$ in the sense of taking the exponent $\lfloor\log_p D\rfloor$. The total logarithmic cost is at most $Y\log D$.
* For $Y<p\le D/Y$, take independent truncated geometric exponents $V_p$ with $\Pr(V_p\ge a)=p^{-\sigma a}$ for $1\le a\le\lfloor\log_p D\rfloor$, and with zero tail beyond that cutoff. Let $S$ denote the logarithm of the small and middle products together. Each middle exponent is at most $3B$. By partial summation of $\vartheta(x)\ll x$, uniformly for $0\le\sigma\le 1-1/B$, $\sum_{p\le x}p^{-\sigma}\log p\ll_B x^{1-\sigma}$. Therefore
$$
 \mathbb E S\ll_B Y\log D+(D/Y)^{1-\sigma}
 \ll_B L^{1/3}\log L+L^{1-1/(3B)}=o_B(\gamma L).
$$
If $S>\gamma L$, replace the entire small and middle product by 1. For any $d\le D$ that has only small and middle factors, before truncating the product its inclusion probability is at least $d^{-\sigma}\ge r$. Conditional on this inclusion, the expected $S$ rises by at most $\log d$. Indeed after conditioning $V_p\ge a$, the remaining exponent is geometric with the same tails and a shorter cutoff, hence stochastically at most the original exponent. This also holds for $\sigma=0$, when exponents are deterministic. Markov's inequality shows a uniform $o_B(1)$ conditional probability of truncation.
* Let $P$ be the number of primes in $(D/Y,D]$. Independently of the previous choices, choose a uniformly random subset of these primes of size
$$
 s=\min\big(P,\lfloor(1-\gamma)L/\log D\rfloor\big).
$$
Their product costs at most $(1-\gamma)L$ in the logarithm. Since $P\sim D/\log D$ uniformly in this range and $L/\log D\to\infty$, each such prime is included with probability $s/P\ge(1-o_B(1))r$. Any $d\le D$ containing one such prime has cofactor $<Y$ and this prime occurs only once, since $D>Y^2$. All primes in the cofactor are included unless the first product was truncated, an event of probability $o_B(1)$ independent of the large-prime choice.

The product after these operations has logarithm at most $L$ and meets the promised marginal bound for every $d$. This proves (1). All little-oh estimates are uniform for the displayed ranges at fixed $B$.

In the counting argument a cover with edges of sizes $2,\ldots,k$ and weight $\sum_E q^{|E|}\le q|C|$ may have up to $q^{1-k}|C|$ edges. The optimized single-difference estimate consequently has error coefficient $K(n,D)q^{1-k}$. In this class of estimates a vanishing coefficient, with $D$ polylogarithmic, requires $Dq^{k-1}/\log n\to\infty$. This specifies the scale at which new structural information about covers would be needed to improve that argument.
