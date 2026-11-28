# Sparse subsets at every interval length

Let $R(n)=r_k(n)$, $M=R(n)$, and $\beta=1/\lceil\log_2 k\rceil$ for a fixed $k\ge3$. Write $I_s(n)$ for the number of $s$-element subsets of $[1,n]$ that avoid nonconstant $k$-term arithmetic progressions. For all integers $1\le s\le M$,
$$
 s\log(M/s)\ \le\ \log I_s(n)\
 \le\ s\log(M/s)+O_k\!\left(s[\log(2M/s)]^\beta\right).           \tag{1}
$$
In particular, $\log I_s(n)\sim s\log(M/s)$ along **every** sequence with $s/M\to0$. The leading term involves $R(n)$. The dependence on this unknown function is essential to the formulation.

For a second consequence, let $S_p$ retain independently each site with probability $p$. Along **every** sequence with $p\to0$ and $pR(n)\to\infty$,
$$
 \frac{\log\big(\alpha_k(S_p)/R(n)\big)}{\log p}\longrightarrow 1
 \quad\text{in probability}.                                      \tag{2}
$$
The logarithm can be assigned any value on the event $\alpha_k(S_p)=0$, whose probability tends to zero. This power-scale estimate complements the ratio-one statement at typical lengths in [the earlier counting note](RothEntropy.md).

## An affine estimate with an adjustable containment probability

A family of subsets covers the progressions of $C\subseteq[1,n]$ if each such progression contains at least one of its members. Suppose the cover has all edges of size between 2 and $k$, with total weight $\sum_g q^{|g|}\le q|C|$, where $0<q\le 1/(8k^2)$. For a constant depending only on $k$,
$$
 |C|\le M\exp\!\left(C_k[\log(2/q)]^\beta\right).                 \tag{3}
$$
We use the random affine progression argument of Morris, Ortega and Rué, keeping the scale dependence from the guarded-digit bound. Their Proposition 5.3 and the proof of Theorem 5.4 supply the coarse iteration below. [Morris–Ortega–Rué](https://arxiv.org/html/2607.17746v1)

Take a prime $2n<P\le4n$ and set $\ell=\max(1,\lfloor Pq^{k-1}/2\rfloor)$. In $\mathbb F_P$ take the image $T$ of $0,\ldots,\ell-1$ under a uniformly chosen invertible affine map. Each point occurs with probability $\ell/P$, and each pair with probability $\ell(\ell-1)/(P(P-1))$. Delete one site from each cover edge contained in $T\cap C$. The surviving indices are progression-free. In fact a $k$-term index progression would give distinct residues in $C$ in modular arithmetic progression. Consecutive second differences of their integer representatives have absolute value at most $2(n-1)<P$, hence vanish in the integers. The original progression contained a cover edge from which a site was deleted. It follows by expectation, using any two distinct sites of each edge, that
$$
 \frac{\ell}{P}|C|\le R(\ell)+|\mathcal G|\frac{\ell(\ell-1)}{P(P-1)}.
$$
Now $|\mathcal G|\le q^{1-k}|C|$, and $(\ell-1)/(P-1)\le q^{k-1}/2$, so $|C|\le 2P R(\ell)/\ell$.

For $n\ge4$, $\ell\le n/4$ and $b=\lfloor n/(2\ell)\rfloor\ge n/(4\ell)$. The digit bound $M\ge R(\ell)R(b)$ and $P/\ell\le16b$ yield $|C|/M\le32b/R(b)$. Also $b\le 4q^{1-k}$, since $\ell\ge Pq^{k-1}/4$, including when the floor is less than one. Apply $b/R(b)\le\exp(C_k[\log(2b)]^\beta)$ from the [Rankin–O'Bryant construction](https://arxiv.org/abs/0811.3057). The bounded smaller values of $n$ are absorbed by the constant. This proves (3).

## A covering family with a prescribed counting cost

For every $0<\theta\le1$, all admissible sets in $[1,n]$ lie in a family of $K$ containers satisfying
$$
 \log K\le C_k\theta M,\qquad
 \max_C |C|\le M\exp\!\left(C_k[\log(2/\theta)]^\beta\right).       \tag{4}
$$
Here are details of both stages. By [Campos–Samotij, Theorem A](https://arxiv.org/html/2408.06617v2), a parent $V$ has children with a cover as in (3) and logarithmic count $O_k(q|V|\log(2/q))$ for sufficiently small $q$. Cover edges larger than $k$ can be discarded. The logarithmic count follows by summing binomial coefficients up to $\lfloor8k^2q|V|\rfloor$, and also holds when this floor is zero.

Start at size ratio $\lambda=n/M$, halving the cap $\lambda M$ until it is at most $L M$, where $L=L_k/\theta$ and $L_k$ is sufficiently large. If the initial cap is already below target there is just one parent. In a halving step with $\lambda>L$, retain parents already of size at most $\lambda M/2$ and refine the rest with $q=\lambda^{-3}$. By (3) each child has size at most $M\exp(C_k[\log(2\lambda^3)]^\beta)\le\lambda M/2$. The logarithmic cost per stage is $O_k(M\log(2\lambda)/\lambda^2)$. Summing over the decreasing dyadic caps gives $O_k(M/L)$.

In the final parents, of size at most $L M$, take $q=c_k\theta^3$ with a sufficiently small positive $c_k$. The additional logarithmic cost is $O_k(M\theta^2\log(2/\theta))=O_k(M\theta)$. Equation (3) gives the claimed container sizes. This proves (4) uniformly, including when the terminal refinement starts at the full interval.

## Counting, random sites and dispersed independent labels

In (4) put $\theta=s/M$. An extremizer gives $\binom Ms\le I_s(n)$; each container of size at most $B$ gives at most $(eB/s)^s$ subsets of size $s$. Use $\binom Ms\ge (M/s)^s$, then take logarithms to obtain (1).

More generally, let independent labels choose output sites in $[1,n]$, and let $Y$ be the set of distinct outputs. Suppose that the sum of the probabilities of choosing any one site is at most $\delta$, with $0<\delta\le1$. A label is also allowed to make no selection. Uniformly for $z>0$,
$$
 \Pr\!\left\{\alpha_k(Y)>
     M\delta\exp(C_k[\log(2/\delta)]^\beta)+z\right\}\le e^{-z}.   \tag{5}
$$
For fixed $C$, let $Z_C$ count labels landing in it, including repeats. Independence gives $\log\mathbb E e^{Z_C}\le(e-1)\mathbb E Z_C\le(e-1)\delta |C|$. Maximize over the containers in (4) with $\theta=\delta$ and apply Markov's inequality and the union bound, absorbing fixed factors in $C_k$. For $S_p$, a label at each site stays with probability $p$ and otherwise makes no selection. For the upper bound in (2) take $\delta=p$ and $z=pM$. A single extremizer retains at least $pM/2$ sites with probability $1-e^{-pM/8}$ or greater. The logarithmic correction in (5) is $o(\log(1/p))$, which proves (2).

There is an all-length and **every-step** conclusion for the displacement experiment in [the companion note](RothExtremalSamples.md). For each $a$ in a free $A\subseteq[1,n]$, choose $a+jt$ independently, uniformly over $0\le j<d$, where $t\ge1$, $d\to\infty$ and $(d-1)t\le n$. At a given output $y$, at most $R(d)$ values $a=y-jt$ lie in $A$ by affine pullback. Thus (5) applies in an interval of length $N\le2n$ with $\delta=R(d)/d\to0$. Also $R(N)\le2R(n)$. If $|A|\sim R(n)$, we obtain $\alpha_k(Y)/|A|\to0$ in probability at every such step, by taking for instance $z=\sqrt{|A|}$. Yet $|Y|/|A|\to1$ in probability. Indeed for occupancy loads $w_y\le\delta$, the expected number of colliding label pairs is at most $\frac12\sum_y w_y^2\le\delta |A|/2$. It takes deletion of a proportion $1-o(1)$ of the **distinct sites** to restore progression-freeness.

## Reproduction and scope

The asymptotic estimates and the covering iteration above are written proofs. [The checker](check_roth_extremal_samples.py) enumerates every invertible affine map and each tested cover for $n=5,6,8$, checking the pointwise deletion inequality before averaging. [The finite Lean proofs](RothExtremalSamples.lean) include fixed-cardinality container bounds, uniqueness of the affine map through two ordered sites, and the absorption inequality after averaging. No assertion here supplies a numerical asymptotic for Erdős 142 itself.
