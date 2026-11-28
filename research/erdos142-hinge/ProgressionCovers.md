# Exact transfer of arithmetic-progression density bounds between interval lengths

Let $r_k(N)$ be the largest size of a subset of $[N]=\{1,\ldots,N\}$ containing no nonconstant $k$-term arithmetic progression. We compute the exact length threshold for transferring the density bound at $n$ to $N$ by uniform covers of $[N]$ with $n$-term progressions. For prime-power $n$ we give the optimum fractional cover at every $N\ge n$. At the exact doubling scale we identify all minimum covers. An adaptive split gives an explicit strict doubling loss at every jump of the Roth number. A separate integer deficit forces a strict doubling loss in every dyadic exponent interval $[j,2j+1]$ for $k=3$.

## An adaptive split and losses at every jump

Write $R=r_3$. There is a stronger transfer for actual progression-free sets, which can choose the two covering intervals after seeing the set:
$$
 R(2m+1)\le 2R(m)\qquad(m\ge1).
$$
At least one of $1,m+1,2m+1$ is absent. Omitting that point leaves all occupied positions covered by two contiguous $m$-point intervals. Iterating this inequality gives
$$
 R(2^j(m+1)-1)\le 2^j R(m)\qquad(j\ge0).
$$
Both inequalities are checked in the companion Lean file for mathlib's actual finite Roth number.

For $n\ge2$ and any positive integer $q$, write $s_2(q)$ for the number of ones in its binary expansion. Split $[qn]$ into one interval of length $2^j n-1$ for each nonzero binary digit indexed by $j$, and one remaining interval of length $s_2(q)$. The preceding result with $m=n-1$ and ordinary subadditivity give
$$
 R(qn)\le qR(n-1)+R\bigl(s_2(q)\bigr). \tag{2}
$$
In particular $R(2n)\le R(n)+R(n-1)$. Indeed monotonicity and one-point extension imply $R(n)-R(n-1)\in\{0,1\}$. In the zero case use ordinary subadditivity, and in the unit case use (2).

At every jump $R(n)=R(n-1)+1$, the loss $qR(n)-R(qn)$ is therefore at least $q-R(s_2(q))$. For $q=2^j$ this is $q-1$. In particular there are at least $R(X)-1$ different $2\le n\le X$ with $R(2n)<2R(n)$. Using the Behrend lower bound gives $X^{1-o(1)}$ such integers. This counts strict integer losses; it does not bound their relative size away from zero. The term “jump” and exact small values are documented by [Dybizbański](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v19i2p15/pdf). The [improved Behrend construction](https://arxiv.org/abs/2406.12290) supplies the cited order of the lower bound. We make no claim of priority for the elementary odd-interval inequality.

There is also a transfer for an arbitrary remainder $r\ge0$. For each $j=0,\ldots,q$ leave the gap $jn+[1,r]$ and use $q$ contiguous $n$-blocks on its complement. Summed over all placements, the gap populations total at most $rR(q+1)$ because the $q+1$ positions attached to each fixed gap offset form one arithmetic progression. This gives
$$
 R(qn+r)\le qR(n)+\left\lfloor rR(q+1)/(q+1)\right\rfloor .
$$
Counting with multiplicity keeps the bound valid even if different placements of the gap overlap.

## A cover with equal weights at every point

Assign a nonnegative real weight to each $n$-term progression in $[N]$ with positive integer difference. A fractional cover brings total weight at least 1 to every point. Write $C_n(N)$ for the minimum sum of the weights. For $2\le n\le N$,
$$
 r_k(N)\le C_n(N) r_k(n),\qquad C_n(N)\ge N/n .
$$
The first bound sums the restriction to each progression and the second counts its $n$ points. The minimum exists in this finite problem. Equality $C_n(N)=N/n$ is equivalent to the existence of a cover bringing exactly 1 to every point.

**Exact threshold.** Such a cover exists precisely when $n\mid N$ or $N\ge n(n-1)+1$.

For necessity, fix a primitive $n$th root of unity $z$. For an $n$-term progression of difference $d$, the sum of $z^x$ over the progression is zero whenever $n$ does not divide $d$. Below the stated threshold all available differences are less than $n$. A uniform cover would force the sum over $[N]$ to be zero, which requires $n\mid N$.

For sufficiency write $N=qn+r$, $0\le r<n$. If $r=0$ partition the interval into $q$ consecutive blocks. Otherwise the threshold gives $q\ge n-1$. For each $j=0,\ldots,n-1$, leave the gap $jn+[1,r]$ and partition its complement into $q$ consecutive $n$-blocks. Give this partition weight $1/n$. For each $i\in[1,r]$ add the progression $i,i+n,\ldots,i+(n-1)n$ with weight $1/n$. Exactly the omitted weight at each gap point is restored. In particular,
$$
 r_k(N)\le \left\lfloor \frac{N r_k(n)}n\right\rfloor\qquad(N\ge n(n-1)).
$$
The sharpness statement concerns the uniform covering method. The numerical inequality for particular extremal functions can also hold at smaller lengths.

## Minimum cover cost at every prime-power length

Suppose $n=p^a$, $a\ge1$. Write $D=\lfloor(N-1)/(n-1)\rfloor$, and let $g$ be the largest power of $p$, including 1, at most $\min(n,D)$. Then
$$
 \boxed{C_n(N)=q+\min(r,g)/g.}
$$

For a lower certificate give weight $1/g$ to each integer whose residue modulo $n$ is one of $1,\ldots,g$ and weight zero to the rest, with residue $n$ representing zero if $g=n$. For any available difference $d$, put $h=\gcd(d,n)$. The prime-power hypothesis implies $h\mid g$. An $n$-term progression visits every residue of one class modulo $h$ exactly $h$ times modulo $n$. Exactly $g/h$ of these residues carry weight $1/g$. Thus the weight of each progression equals 1. The total point weight is the claimed lower bound on cover cost.

For the upper certificate, if $r=0$ use the partition. If $r\ge g$ cover by $q$ consecutive blocks and one block ending at $N$. If $0<r<g$, use the gap construction above with just $j=0,\ldots,g-1$ and weight $1/g$. For each $i\in[1,r]$ add the $n$-term progression starting at $i$ with difference $g$, also with weight $1/g$. It contains every omitted point $i+jn$ for that $i$ since $g\mid n$ and $(g-1)n/g\le n-1$. Overcoverage is permitted.

Here all progressions fit. For $g=n$ this follows from $q\ge n-1$. For $g<n$ we have $n\ge2g$. If $q\le g-1$ and $r<g$, then $N\le(g-1)n+g-1<g(n-1)+1$, contrary to $g\le D$. Therefore $q\ge g$ and the largest added point is at most $r+(n-1)g\le N$. When $n$ is prime and $n\nmid N$, the cost is the full ceiling $\lceil N/n\rceil$ throughout the range below the uniform-cover threshold.

## What minimum covers use at doubling

For every $n\ge3$, the only minimum covers of $[2n]$ by $n$-term progressions are convex combinations of the partition into two halves and the partition into even and odd points. To see this, minimum cost is 2 and hence coverage is exactly 1 everywhere. Differences 1 and 2 exhaust the possibilities. Give the two step-2 progressions weights $o,e$ for odd and even, and the contiguous intervals weights $x_1,\ldots,x_{n+1}$ by their starts. Comparing coverage at points 1, 2 and 3 gives $x_2=o-e$ and $x_3=e-o$. Nonnegativity forces $e=o$. Comparing successive points up through $n$ now gives zero for all interior starts. The two edge intervals each carry $1-o$. This also proves that any argument using only nonnegative averages of the scalar capacity $r_k(n)$ at doubling cannot yield a strict upper bound without additional information.

## A strict drop forced by the progression-free condition

Put $T=n(n-1)$ and assume $k\ge3$, $n\ge2$, $N\ge T$. Then
$$
 r_k(N)\le \left\lfloor \frac Nn r_k(n)\right\rfloor-
          \left\lfloor \frac{N-T}{kn+T}\right\rfloor. \tag{1}
$$
Every slab of $kn$ consecutive points contains an $n$-point window with at most $r_k(n)-1$ members of any $k$-progression-free set. Otherwise every one of its windows contains exactly $r_k(n)$. Subtracting adjacent counts gives $1_A(i+n)=1_A(i)$ throughout the slab wherever both indices occur. Any occupied position in the first window then repeats $k$ times with difference $n$, a contradiction. That window is nonempty since $r_k(n)\ge1$.

Take $m=\lfloor(N-T)/(kn+T)\rfloor$ slabs separated by buffers of length $T$, with a buffer of at least $T$ on each outside edge. When $m=0$ the equal-weight cover already proves (1). Otherwise select one deficient window per slab. Each complementary interval has length at least $T$ and hence admits an exact uniform cover. Count the selected windows with weight 1 and complete the cover on their complement. Its cost is $N/n$, and each selected window saves at least one point. This proves (1).

In particular, let $k=3$, $n=2^j$, $j\ge1$, $N=4n^2$. At least one unit is saved. Consequently at least one $i$ with $j\le i\le2j+1$ satisfies $r_3(2^{i+1})<2r_3(2^i)$. Otherwise all densities in that range of doublings would be equal, including those at $n$ and $N$. This gives a finite restriction on long strings of exact equalities. It leaves the size of the relative loss and the ratio-one asymptotic undetermined.

The accompanying standard-library script constructs 567 uniform covers and 1,330 matching prime-power primal and dual certificates. It checks interval membership, every point's coverage, and the residue weights of every available progression up to periodicity. These checks supplement the general proofs above.
