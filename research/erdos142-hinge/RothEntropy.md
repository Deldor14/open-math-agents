# Counting progression-free sets at almost every logarithmic scale

**Research note for review.** For fixed $k\ge3$, let $M=r_k(n)$ be the maximum size of a subset of $[n]$ with no nonconstant $k$-term arithmetic progression, and let $I_k(n)$ be the number of all such subsets, including the empty set. We prove that on a set of lengths of logarithmic density one,
$$
 M\le \log_2 I_k(n)\le M\left(1+O_k\!\left(\frac{(\log\log n)^2}{\sqrt{\log n}}\right)\right). \tag{1}
$$
The exceptional set may depend on $k$. In particular this includes three- and four-term progressions. Averaged over *all* lengths there is the estimate
$$
 \sum_{2\le n\le X}\frac1n\left(\frac{\log_2 I_k(n)}{r_k(n)}-1\right)
 \ll_k \sqrt{\log X}\log\log X \qquad (X\text{ sufficiently large}). \tag{2}
$$
All unsubscripted logarithms are natural. Logarithmic density one means that the exceptional lengths contribute $o(\log X)$ to the sum of $1/n$ up to $X$.

The Cameron–Erdős counting question asks for the equivalent in (1) at every length. For context, Morris, Ortega and Rué give the leading coefficient one along an infinite sequence for $k\ge5$ and a bounded coefficient for all lengths and all $k\ge3$. Here the improvement at typical scales comes from stopping an initial container iteration while its containers may still have a growing multiple of $M$ vertices. The last, more accurate refinement then costs $o(M)$ bits even when $k=3,4$. The estimates still involve the unknown extremal function in Erdős problem 142. [Morris–Ortega–Rué, Theorems 1.3–1.4 and Question 7.1](https://arxiv.org/html/2607.17746v1)

## A finite supersaturation inequality

A family $\mathcal G$ covers the $k$-term progressions in $C\subseteq[n]$ if each progression contains a member of $\mathcal G$. Consider covers whose edges have at least two points. Edges larger than $k$ can always be discarded. For $0<q<1$ write $w_q(\mathcal G)=\sum_{E\in\mathcal G}q^{|E|}$. For $D\ge2$ integer put $K_D(n)=\max_{p\le D,\ p\text{ prime}} p\,r_k(\lceil n/p\rceil)$ and let $\pi(D)$ count primes up to $D$. Then, for $n\ge2$,
$$
 \pi(D)\big(|C|-K_D(n)\big)_+\le \lfloor\log_2 n\rfloor\, |\mathcal G|. \tag{3}
$$
For each prime $p$, delete one vertex from every cover edge contained in a residue class mod $p$. The remaining points in each class avoid $k$-term progressions and, after rescaling, lie in an interval of at most $\lceil n/p\rceil$ sites. At least $(|C|-K_D(n))_+$ deletions are necessary. Fix two distinct points in each cover edge, with difference $d$ between 1 and $n-1$. That edge lies in a single class only when $p\mid d$, which happens for at most $\lfloor\log_2 n\rfloor$ primes. Summing proves (3). In particular the number of progressions themselves satisfies the same lower bound on $|\mathcal G|$. Allowing pairs and other subedges is essential to the application below.

For a cover with $w_q(\mathcal G)\le q|C|$, retain only its edges of sizes $2,\ldots,k$. Each retained edge has weight at least $q^k$. Hence
$$
 (1-\rho)|C|\le K_D(n),\qquad
 \rho=\frac{\lfloor\log_2 n\rfloor}{\pi(D)q^{k-1}}
 \ll \frac{\log n\log(2D)}{Dq^{k-1}}. \tag{4}
$$
The last bound needs only the elementary prime estimate $\pi(D)\gg D/\log(2D)$. For example $\binom{2m}{m}\ge 4^m/(2m+1)$, while each of its prime-power factors $p^{v_p}$ is at most $2m$ by the factorial valuation formula. Take $m=\lfloor D/2\rfloor$.

We use Theorem A of Campos and Samotij on the $k$-uniform hypergraph of progressions induced by a finite vertex set $V\subseteq[n]$. For $0<q\le1/(8k^2)$, all independent sets are contained in containers indexed by subsets of $V$ of size at most $8k^2q|V|$. Every resulting container $C$ has a cover as in (4). Thus for sufficiently small $q$ the logarithm of the number of children is $O_k(q|V|\log(1/q))$ by the binomial bound. All uses of this theorem below have $q\to0$. [Campos–Samotij, Theorem A](https://arxiv.org/html/2408.06617v2#S1)

## Two refinements

Set $j=\lfloor\log_2 n\rfloor$. We give estimates uniform for $\log(j+2)\le u\le\sqrt j$ as $j\to\infty$, with $k$ fixed. Put $L=e^{4u}$. First shrink to containers of size at most $LM$. The argument only uses the [Behrend-type lower bound](https://arxiv.org/abs/2406.12290) in the form $r_k(m)\ge r_3(m)\ge m\exp(-O(\sqrt{\log(2m)}))$.

For positive $a,b$, $r_k(2ab)\ge r_k(a)r_k(b)$. In zero-based coordinates use low digit $x<a$ and high digit $y<b$ in $x+2ay$, with both digit sets $k$-AP-free. A zero second difference of three consecutive terms forces zero second difference separately in both digits, since the low difference has magnitude less than $2a$. A nonconstant $k$-AP would thus give a nonconstant $k$-AP in at least one digit. For $4\le p\le n$, take $a=\lceil n/p\rceil$ and $b=\lfloor p/4\rfloor$, giving $2ab\le n$. Consequently, uniformly for $2\le D\le n$,
$$
 K_D(n)/M\le \exp(O(1+\sqrt{\log D})). \tag{5}
$$
Indeed $pr_k(a)/M\le p/r_k(b)$, and $p=2,3$ satisfy a constant bound directly.

If $n/M\le L$ use $[n]$ as the only initial container. Otherwise start at $\lambda=n/M$ and successively halve $\lambda$ until $\lambda\le L$. At a stage $\lambda>L$ all parents have size at most $\lambda M$. Parents already below $\lambda M/2$ may be retained. For the others apply the container theorem with $q=\lambda^{-3}$ and put $D=\lceil\lambda^{4k+4}\rceil$. As $\lambda\le n/M\le\exp(O(\sqrt{\log n}))$, we have $D\le n$ for large $n$. By (5), $K_D(n)=o(\lambda M)$ uniformly for $\lambda>L$. In (4) the error is $O_k(j\log\lambda/\lambda^{k+7})=o(1)$, since $L\ge(j+2)^4$. Therefore every child has size at most $\lambda M/2$. The logarithmic cost per stage is $O_k(M\log\lambda/\lambda^2)$. The dyadic sum, starting from its smallest scale in $(L,2L]$, is $O_k(M\log L/L^2)$.

For the last refinement use $q=e^{-10u}$ on each parent of size at most $LM$ and put $D=\lceil\exp((10k+10)u)\rceil$. The additional logarithmic cost is $O_k(Mu e^{-6u})$. In (4), $Dq^{k-1}\ge e^{20u}$ and $\log n\ll j\le e^u$, so $\rho=O_k(e^{-17u})$. Altogether the resulting family covers all progression-free sets and satisfies
$$
 \log|\mathcal C|\ll_k M e^{-5u},\qquad
 |C|\le (1+O_k(e^{-17u}))K_D(n) \quad(C\in\mathcal C). \tag{6}
$$

## The variation of the extremal density

Put $G(i)=\log(2^i/r_k(2^i))$. Splitting into halves makes $G$ nondecreasing and Behrend gives $G(i)=O(\sqrt{i+1})$. Set $h=\lceil(20k+40)u/\log 2\rceil$, $a=2^{j-h}$, $B=2^{j+h}$ and $v=G(j+h)-G(j-h)$. For large $j$ we have $h<j/2$. Partitioning intervals into $a$-blocks gives
$$
 p\,r_k(\lceil n/p\rceil)\le (n+p a)\,r_k(a)/a .
$$
This follows also from $\lceil\lceil n/p\rceil/a\rceil=\lceil n/(pa)\rceil$. Partitioning $[B]$ into $n$-blocks gives $M/n\ge (r_k(B)/B)/(1+n/B)$. Since $D a/n$ and $n/B$ are both $O_k(e^{-u})$, this proves
$$
 K_D(n)/M\le e^v(1+O_k(e^{-u})). \tag{7}
$$

For (1)–(2), take large powers of two $J$ and, simultaneously for $J\le j<2J$, set $u=\log(2J+2)$. Each increment of $G$ enters at most $2h$ of the differences $v$. Hence $\sum_{J\le j<2J}v\ll_k\sqrt J\log J$. At most $O_k(J/\log J)$ exponents have $v>(\log J)^2/\sqrt J$. On all other shells, (6)–(7) and $2^M\le I_k(n)\le |\mathcal C|2^{\max|C|}$ give (1) throughout $2^j\le n<2^{j+1}$. The lower bound counts all subsets of one extremal set.

For (2), on any shell with $v\le1$ the normalized excess in (2) is $O_k(v+e^{-u})$. On shells with $v>1$ use the all-length estimate $\log I_k(n)=O_k(M)$ of Morris–Ortega–Rué, Theorem 1.4. The supremum of the normalized excess on *each* shell is therefore $O_k(v+e^{-u})$. The harmonic weight of a shell is bounded by a constant. Sum first over $J\le j<2J$, then geometrically over the dyadic blocks of exponents up to $\log_2 X$. This proves (2).

## What this gives for the original extremal quantity

Take $u=\log(2j+2)$ and $h=\lceil(20k+40)u/\log 2\rceil$. Equations (6)–(7) have no exceptional-set hypothesis. Therefore if $G(j+h)-G(j-h)\to0$ over all $j$, then $\log_2 I_k(n)\sim r_k(n)$ over all $n$. For example this condition would follow from an actual ratio-one asymptotic $r_k(n)\sim A n(\log n)^b\exp(-c\sqrt{\log n})$ with fixed $A,c>0$ and real $b$. Indeed the change in the square root on this window is $O_k(\log j/\sqrt j)$, and the error in its logarithm from a ratio-one asymptotic is $o(1)$. This is a conditional implication of an explicit smooth profile.

There is also a sampling interpretation on the good shells in (1). If $U_n$ is drawn uniformly from the $I_k(n)$ admissible sets, then $2\mathbb E|U_n|\sim r_k(n)$. In fact for each fixed $0<\eta<1/2$, the probability that $\big||U_n|/M-1/2\big|>\eta$ is at most $\exp(-c_\eta M)$ for all sufficiently large good lengths. Each container embeds in a set of $s=\lceil(1+o(1))M\rceil$ sites, using a common upper bound $s$ for the family. Within such a set the number of subsets outside the indicated sizes is at most $2^s\exp(-c'_\eta s)$ by the two binomial tail bounds. There are $\exp(o(M))$ containers and at least $2^M$ admissible sets. Boundedness of $|U_n|/M$ gives the expectation claim.

## A second derivation of the deterministic estimate (1)

One can replace the prime-counting argument by two results within the proof of Morris–Ortega–Rué. In their proof of Theorem 5.4, intermediate scales have $|C|\le\lambda_i M$, $\lambda_i=(n/M)2^{1-i}$, with logarithmic growth in the number of containers at most $O_k(M/\lambda_i)$ and full coverage (properties (a)–(c), around their equation (22)). Stop at the first $\lambda_i\le J^2$, or use the root if already smaller. The number of parents has logarithm $O_k(M/J^2)$.

On the good shells above let $\ell=\lfloor n/J^{20k}\rfloor$. The choices of $a,B,h$ give $a/\ell\ll_k J^{-1}$ and $n/B\ll J^{-1}$. Applying the two interval partitions to $\ell$ and $n$ shows $r_k(\ell)/\ell\le (1+O_k((\log J)^2/\sqrt J))M/n$. Take $\delta=C_k(\log J)^2/\sqrt J$ with a sufficiently large constant. This verifies hypothesis (9) in Proposition 4.1 of the same paper. With $q=J^{-4}$ its hypothesis (10) holds because $\log n\,\delta^{-2}(\ell/n)^{1/(2k)}\ll_k J^{-8}$. The last container refinement inside each parent costs $O_k(J^{-2}M\log J)$ in the logarithm. By the proposition, a child with a $q$-weight cover of weight at most $q|C|$ has size less than $(1+\delta)M$. This independently recovers (1) from those propositions; both derivations use the general container theorem. [Proposition 4.1 and proof of Theorem 5.4](https://arxiv.org/html/2607.17746v1)

## Randomly retained sites

Let $0<p_n\le1$ be any prescribed sequence with $\log(1/p_n)=o(\sqrt{\log n})$. Retain each site of $[n]$ independently with probability $p_n$ to obtain $S_n$. Along a set of lengths of logarithmic density one, possibly depending on the sequence,
$$
 \alpha_k(S_n)/(p_n r_k(n))\longrightarrow 1\quad\text{in probability}.
$$
Here $\alpha_k$ is the largest $k$-AP-free subset size. On $J\le j<2J$ take $u$ to be the maximum of $\log(2J+2)$ and of $\log(1/p_n)$ over the corresponding lengths. Then $u=o(\sqrt J)$, $h=O_k(u)$ and the mean $v$ is $O_k(u/\sqrt J)=o(1)$. Discarding $o(J)$ shells gives $v=o(1)$ there, by Markov's inequality with threshold $(u/\sqrt J)^{1/2}$. On the remaining shells, (6)–(7) provide containers of size at most $(1+o(1))M$ and logarithmic count $o(p_nM)$. For any fixed $\epsilon>0$, a binomial upper-tail bound and a union bound over containers exclude sizes larger than $(1+\epsilon)p_nM$ with probability tending to one. A lower-tail bound on a fixed extremal set gives the reverse estimate. Behrend ensures $p_nM\to\infty$. The probability statement is pointwise in the lengths of the indicated set.

The companion Lean file checks the prime-divisor multiplicity and the associated finite incidence sum. The analytic estimates and container applications are proved in writing above. Run `python3 check_roth_entropy.py` to reproduce the small enumerations. At $n=12$ the counts for $k=3,4,5$ are 705, 2,233 and 3,345. The script also checks 36,864 cover instances using whole progressions, pairs and mixed edge sizes, including 1,173 with positive summed excess.
