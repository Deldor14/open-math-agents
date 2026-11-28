# Prescribed points, disjoint packings and local density in almost extremal Roth sets

Let $R(N)=r_3(N)$, the maximum size of a three-term-progression-free subset of $[N]=\{1,\ldots,N\}$. The following ratio-one results use the genuine finite Roth number. They apply without a regular-variation assumption on it.

* If $kR(N)=o(N)$, one can place $k$ disjoint progression-free subsets of $[N]$, each of size $(1-o(1))R(N)$. Equivalently the greatest size of a $k$-colorable partial subset is asymptotic to $kR(N)$ throughout this range. There is no requirement on progressions mixing different colors.
* One may forbid any $o(N)$ specified points and require any disjoint progression-free set of $o(N/R(N))$ specified points, at arbitrary locations. The maximum constrained size is still $(1-o(1))R(N)$.
* There exists a single infinite progression-free set that is simultaneously near-maximal in **every** sufficiently long subinterval of each of an unbounded sequence of boxes. In particular, its prefix cardinality divided by $R(N)$ has limsup one. Initial finite membership and nonmembership prescriptions may be imposed.

These conclusions give reductions and structural restrictions. They do not determine the asymptotic size of $R(N)$.

## Two finite inequalities

Write $M=R(N)$. We use the digit bound
$$
 R(2ws)\ge R(w)R(s)\qquad(w,s\ge1).
$$
With zero-based coordinates take the points $a+2wb$ for $a,b$ in respective optimal sets. The low-digit second difference has absolute value less than $2w$, so a progression requires zero second difference in both digits and is trivial. It follows that $R(w)/M\le 1/R(\lfloor N/(2w)\rfloor)$ when $2w\le N$. This tends uniformly to zero as $N/w$ tends to infinity.

For any $1\le w\le N$, translate a fixed optimal set $A$ by $t$ uniform in $\{0,\ldots,w-1\}$. On cutting the translate back to $[N]$ at most $R(w)$ points are lost. For a fixed used set $U\subseteq[N]$, a given $u\in U$ is hit by at most $R(w)$ translates. Indeed the possible preimages $u-t$ lie in one interval of $w$ points. The mean overlap is therefore at most $|U|R(w)/w$. Removing the used points and successively choosing a translate of at most mean overlap gives, for every one of $k$ color classes, a cardinality at least
$$
 M-R(w)-(k-1)M R(w)/w.
$$
Set $w=kM$ when $kM\le N$. Each class has at least $M-2R(kM)$ points. The digit inequality proves the first assertion for all $k=k(N)$ in the stated range. The converse cardinality bound $kM$ follows by restriction to each class.

**Arbitrary locations of required and forbidden points.** Let $F,T\subseteq[N]$ be disjoint, with $F$ progression-free and $f=|F|$. Delete from the new translate all points of $T$, all points of $F$ (which will be added back), and all possible third points of a nonconstant progression through two distinct members of $F$. Their union $U$ has size at most $|T|+f+3\binom f2$. Its mean intersection with the translate is at most $|U|R(w)/w$.

The remaining obstructions have exactly one required point $p$ and two new points $y+t,z+t$. With $p$ an endpoint and $y+t$ the midpoint, the equation is $z=2y+t-p$. With $p$ the midpoint, it is $z=2p-y-2t$. For a fixed $(p,y)$ the possible $z\in A$ in either equation form a subset of a progression of length $w$ and difference 1 or −2. Hence at most $R(w)$ choices of shift can work in either equation. The mean number of incidences in the two cases together is at most $2fM R(w)/w$. Each incidence can be eliminated by deleting one new point. Choosing a shift for which the *total* loss is at most its mean and adjoining $F$ proves the finite bound
$$
 |B|\ge M+f-R(w)\left(1+\frac{|T|+f+3\binom f2+2fM}{w}\right),
 \quad F\subseteq B\subseteq[N]\setminus T. \tag{2}
$$
The resulting $B$ is progression-free. The argument permits some forbidden or deleted candidates outside $[N]$, which can only enlarge the loss estimate.

Suppose $|T|=o(N)$ and $(1+f)M=o(N)$. By Behrend, $M=N^{1-o(1)}$, so $f^2=o(N)$. Choose $w$ to be the maximum of 1 and the numerator in (2). Then $w=o(N)$ and eventually $w\le N$. The digit bound makes $2R(w)=o(M)$, uniformly along every sequence with these hypotheses. Thus the largest possible constrained cardinality is $(1-o(1))M$. In particular puncturing *any* $o(N)$ sites causes only a relative $o(1)$ loss, even when the number removed is much larger than $M$. Prescribing the exact prefix $F\subseteq[b]$ follows by taking $T=[b]\setminus F$.

## One infinite configuration, many lengths at once

Here is a quantitative version. There is an infinite progression-free set $A$ and an unbounded sequence of integers $j$ such that, with $n=2^j$, every interval $I\subseteq[n]$ of length $x\ge n j^{-1/16}$ obeys
$$
 |A\cap I|\ge (1-O(j^{-1/16}))R(x). \tag{1}
$$
Initial finite prescriptions may be arbitrary provided the prescribed positive set is progression-free.

For the choice of scales put $G(j)=\log(2^j/R(2^j))$. Splitting into halves shows $G$ is nondecreasing, and the Behrend lower bound gives $G(J)=O(\sqrt J)$. Set $h=\lfloor j^{1/4}\rfloor$, $L=2^{j-h}$ and $\lambda_j=G(j)-G(j-h)$. Up to $J$, each increment of $G$ contributes to at most $1+\lfloor J^{1/4}\rfloor$ losses, so their sum is $O(J^{3/4})$. Only $O(J^{7/8})$ exponents have $\lambda_j>j^{-1/8}$.

Starting from any fixed previous prefix $(b,F)$, choose an arbitrarily large good exponent $j$ at which the extension lemma gives $|B|\ge(1-j^{-1/8})R(n)$. Such exponents exist. Indeed $R(n)\ge n^{1-o(1)}$ and $n/R(n)\ge\exp(c j^{1/9})$ by Bloom–Sisask. For the fixed old prefix the $w$ in (2) is $O_{b,F}(1+R(n))$, so $R(w)/R(n)$ is exponentially small in a positive power of $j$ by the digit bound and $R(s)\ge s^{1-o(1)}$. Freeze the prefix $B$ on $[n]$ and repeat. Every potential forbidden triple in the resulting union would already be in a frozen prefix.

To check (1), put $U=R(L)$. The complement of $I$ in $[n]$ has at most two components and can be partitioned into at most $(n-x)/L+2$ intervals of length at most $L$. Also $R(n)=(n/L)Ue^{-\lambda_j}$ and $R(x)\le(x/L+1)U$. Subtraction in the frozen prefix gives
$$
 |A\cap I|\ge (U/L)\{x-n(j^{-1/8}+\lambda_j)-2L\}.
$$
Division by the upper bound for $R(x)$ yields (1). In particular every such box contains a run of consecutive dyadic prefix lengths with ratios tending uniformly to one, and the number of lengths in those runs tends to infinity.

The infinite limsup assertion alone needs only the extension lemma and $R(n)=o(n)$; the stronger all-subinterval estimate uses the quantitative upper bound. Sources for the bounds are [Elsholtz, Hunter, Proske and Sauermann](https://arxiv.org/abs/2406.12290) and [Bloom and Sisask](https://arxiv.org/abs/2309.02353). The companion Lean file proves the digit inequality for mathlib's finite Roth number and the finite double count used for overlaps.
