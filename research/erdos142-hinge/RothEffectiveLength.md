# A two-sided sparse Szemerédi estimate at every length and density

Fix $k\ge3$. Write $R(n)=r_k(n)$ for the largest size of a subset of $[1,n]$ avoiding nonconstant $k$-term arithmetic progressions, and $\alpha(S)$ for the maximum on an available set $S$. Retain sites independently with probability $0<p\le1$ to obtain $S_p$. Put
$$
 b=\lceil np^{k-1}\rceil,\qquad \delta_b=R(b)/b,\qquad T=np\delta_b.
$$
For every integer $n\ge1$,
$$
 T/10\le\mathbb E\alpha(S_p)\le C_kT,\qquad
 (\log2)T/10\le\log Z_n(p)\le C_kT,\qquad
 Z_n(p)=\sum_{I\subseteq[1,n],\ I\ {\rm free}}p^{|I|}.             \tag{1}
$$
There is also a two-sided probability estimate:
$$
 \Pr\{\alpha(S_p)<T/20\}\le e^{-T/400},\qquad
 \Pr\{\alpha(S_p)\ge h\}\le 2^{-h}e^{C_k T}.                        \tag{2}
$$
In particular the typical largest free set has order $np\,R(b)/b$ whenever $T\to\infty$. The same order holds when the sample size $m=np$ is a prescribed integer. All constants in upper estimates may depend on $k$ alone.

For three terms, $b=\lceil np^2\rceil$. For instance, keeping sites with probability $m^{-1/2}$ in an interval of length $m^2$ gives an expected maximum of order $\sqrt m\,r_3(m)$. The deterministic extremal function on the right is unknown. The estimate identifies its role in a different random problem uniformly up to fixed factors.

The qualitative sparse Szemerédi theorem was established by Kohayakawa–Łuczak–Rödl for three terms and by Conlon–Gowers and Schacht for general length. Balogh–Liu–Sharifzadeh gave quantitative transference bounds. The upper proof here uses the affine restriction in the counting work of Morris–Ortega–Rué and the fingerprint theorem of Campos–Samotij. Our [previous comparison](RothCriticalSampling.md) identified a worst-case ratio over hosts for a given $p$. Formula (1) gives both inequalities at the specified ambient length $n$. [Conlon–Gowers](https://annals.math.princeton.edu/wp-content/uploads/annals-v184-n2-p02-p.pdf), [Balogh–Liu–Sharifzadeh](https://arxiv.org/abs/1605.03172), [Morris–Ortega–Rué](https://arxiv.org/html/2607.17746v1), [Campos–Samotij](https://arxiv.org/html/2408.06617v2).

## Upper estimate using the actual length of an affine sample

Take $2n<P\le4n$ prime, interpreting bounded $n$ by the same estimates. At a stage with parameter $0<q\le1/(8k^2)$ the container theorem gives a cover $\mathcal G$ of the progressions in each child $C$ by subedges, of sizes $2,\ldots,k$ after unused larger edges are discarded, with $\sum_{g\in\mathcal G}q^{|g|}\le q|C|$. Sample the image of an interval of length $\ell=\max(1,\lfloor Pq^{k-1}/2\rfloor)$ by a uniform invertible affine map in $\mathbb F_P$. Any index progression mapping wholly into $C$ is a genuine integer progression in $C$, as its consecutive second differences have magnitude less than $P$. Delete one site from each cover edge wholly in the sample. The point and ordered-pair inclusion probabilities give
$$
 \ell |C|/P\le R(\ell)+|\mathcal G|\ell(\ell-1)/(P(P-1)),
 \qquad |C|\le 2P\,R(\ell)/\ell.                                   \tag{3}
$$
The second inequality uses $|\mathcal G|\le q^{1-k}|C|$ and $(\ell-1)/(P-1)\le q^{k-1}/2$. The [affine restriction proof](RothAllLengthSampling.md) contains details.

Set $q_i=p\,2^{-4i}/(16k^2)$, $i=0,1,\ldots$. The sampled length satisfies $\ell\le b$ and $b/\ell\le C_k2^{4(k-1)i}$. For the latter, use $\ell\ge P q_i^{k-1}/4$, or use $b=1$ if $np^{k-1}\le1$. If $b<2\ell$ then $\delta_\ell\le2\delta_b$. Otherwise $a=\lfloor b/(2\ell)\rfloor$ satisfies $R(b)\ge R(\ell)R(a)$ by the separated-digit product, and $b/\ell\le4a$. Thus
$$
 \delta_\ell/\delta_b\le 4a/R(a)\le\exp(O_k((1+i)^\beta)),
 \qquad \beta=1/\lceil\log_2 k\rceil<1 .
$$
The last step uses the [Rankin–O'Bryant lower bound](https://arxiv.org/abs/0811.3057). Since the last expression is at most a constant times $2^i$, (3) bounds **every** child at stage $i$ by $W2^i$ sites, where $W=A_k n\delta_b$. The constant $A_k$ is chosen once.

Descend through the caps $W2^{i+1},W2^i$, starting above the full interval, stopping at $W$. For any free set $I$ in a parent $V$, the theorem supplies an actual fingerprint $F\subseteq I$ with $I$ in its child. Remove $F$ at the next stage. Writing $a=2^i$, $T_0=pW$, the bound $|F|\le8k^2q_i|V|$ gives $|F|\le T_0/a^3$, while $p|V|\le2T_0 a$. The sum of the weights $p^{|F|}$ of possible fingerprints in one parent is at most
$$
 (a^2)^{T_0/a^3}(1+p/a^2)^{|V|}\le \exp(3T_0/a).
$$
Indeed $\log(a^2)\le a^2$. Each fingerprint site contributes to the weight only once, by its removal. Terminal powersets cost at most $\exp(T_0)$. Since $\sum_{i\ge0}2^{-i}=2$, the whole partition function is at most $\exp(7T_0)$. If the root already fits, the terminal powerset bound suffices. For Bernoulli retention $Z_n(p)$ is the expected number of free subsets of the sample, which is at least $\mathbb E2^{\alpha(S_p)}$. Jensen and Markov give the upper halves of (1)–(2).

## A residue construction giving the reverse inequality

Choose a free set $D\subseteq[0,b)$ of size $R(b)$. In $\mathbb Z/(2b)$ a progression contained in $D$ must be constant. Indeed integer representatives of all consecutive second differences have absolute value less than $2b$. They vanish, and either orientation of a nonconstant integer progression in $D$ is forbidden. This property is preserved by translation in the cyclic group.

Averaging over translates of $D$, choose one whose residue classes in $[1,n]$ contain altogether $v\ge n\delta_b/2$ sites. In each occupied class there are at most $u=\lceil n/(2b)\rceil$ available sites. Free choices within the separate classes combine to a free subset of the interval, since every progression in their union lies in one class.

In a class of actual length $l\le u$, thin with probability $p/4$. Delete at most one point for each surviving progression. The expected free size is at least
$$
 l(p/4)-l^2(p/4)^k\ge lp/5 .
$$
Here $l p^{k-1}\le3/2$ and $k\ge3$. A coupling gives the same lower bound for the expected maximum at retention $p$. Summing gives $\mathbb E\alpha(S_p)\ge pv/5\ge T/10$. Jensen gives the partition-function lower bound in (1).

For the lower tail let $f$ be the sum of the within-class maxima. Revealing the $v$ Bernoulli variables gives martingale increments of the form $(\xi-p)d$, where $0\le d\le1$ conditionally on the past. This follows from monotonicity and the effect of changing one site. For $\lambda\ge0$ the conditional negative exponential moment is at most $\exp(p(\lambda d-1+e^{-\lambda d}))\le\exp(p\lambda^2/2)$. Multiplication and optimization give $\Pr(f<\mathbb E f-x)\le\exp(-x^2/(2pv))$. With $x=pv/10$ this proves (2).

For a uniform sample of exactly $m$ sites, a fixed $j$-set is present with probability at most $p^j$, $p=m/n$, preserving the partition-function upper bound for the sample's subsets. Mark the sampled sites independently with probability $1/4$ in the lower construction. The marginals are $p/4$ and each progression occurs with probability at most $(p/4)^k$, giving the same expectation lower bound. For a high-probability lower bound, couple the uniform sample with the $p/2$ Bernoulli sample by taking initial segments of the same uniform permutation with their respective sizes. The probability that the latter size exceeds $m$ is at most $e^{-c m}$. Its effective length $b'=\lceil n(p/2)^{k-1}\rceil$ satisfies $b'\le b$, hence $\delta_{b'}\ge\delta_b/2$ by partitioning $[b]$ into intervals of length $b'$. Applying (2) gives probability $1-O(e^{-cT})$ for a lower bound of order $T$.

## Reading off the deterministic density from a sparse experiment

For an integer $b\ge1$, take $p=(b/n)^{1/(k-1)}$ over $n\ge b$. Both the lower limit and the upper limit as $n\to\infty$ of $\mathbb E\alpha(S_p)/(np)$ lie between $c_k\delta_b$ and $C_k\delta_b$, with constants independent of $b$. In particular the negative logarithm of either limit differs from $\log(b/R(b))$ by $O_k(1)$. The sparse observable uses the cardinality of the input in expectation for its normalization and involves no deterministic extremal number. Formula (1) does not determine whether the two limits coincide for each $b$.

## Fixed-cardinality counts to additive error of order the rank

Write $I_s(n)$ for the number of free $s$-sets, $\gamma=(k-2)/(k-1)$, and take $K=800$. For $1\le Ks\le R(n)$ define $p_0$ as follows. If $Ks\le n^\gamma$, put $p_0=Ks/n$. Otherwise let $b_0$ be the first integer $b$ with $n^\gamma R(b)/b^\gamma\ge Ks$ and put $p_0=(b_0/n)^{1/(k-1)}$. Then
$$
           \log I_s(n)=s\log(1/p_0)+O_k(s).                        \tag{4}
$$
In the first case the effective length is one and $T=Ks$. In the second case $b_0$ exists since the endpoint gives $R(n)$, and $Ks\le T\le2Ks$ since $R(b)\le R(b-1)+1\le 2R(b-1)$ for $b\ge2$. For both cases $I_s(n)p_0^s\le Z_n(p_0)\le\exp(O_k(s))$. On the other hand $I_s(n)p_0^s$ is the expected number of free $s$-sets in the sample, hence is at least $\Pr(\alpha(S_{p_0})\ge s)\ge 1-e^{-2}$. This proves (4). For the remaining ranks $R(n)/K<s\le R(n)$ one always has $0\le\log I_s(n)\le O_k(s)$ by (1) at $p=1$.

If $s=o(R(n))$ in the second case then $b_0=o(n)$. For each fixed integer $L$, partition into blocks of length $\lfloor n/L\rfloor$ to see that $n^\gamma R(\lfloor n/L\rfloor)/\lfloor n/L\rfloor^\gamma\gg_L R(n)$. Thus the first crossing lies before $n/L$ eventually. In this range (4) locates the controlling scale using only values of $R$ at lengths strictly below $n$ and gives $\log I_s(n)\sim s\log(n/b_0)/(k-1)$.

## Verification

[The Lean source](RothEffectiveLength.lean) checks regrouping by fingerprints, the full finite weighted iteration and the bound $\exp(7T_0)$ under its explicit stage and terminal hypotheses, progression-freeness of the residue union for general $k$, and the deletion arithmetic. The identification of these hypotheses with the external container theorem, the scale comparison, and the probability and asymptotic deductions have written proofs. [Exact enumerations](check_roth_effective_length.py) check both sampling models, the residue construction, and the affine estimate on small instances. The explicit ratio-one asymptotic in Erdős 142 remains open.
