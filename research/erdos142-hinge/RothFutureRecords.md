# How often does the finite Roth number sustain growth at every later length?

Let $R(n)$ denote the largest cardinality of a subset of the first $n$ integers avoiding nonconstant three-term arithmetic progressions. Say $j$ is a record for exponent $0<\alpha<1$ if
$$
 R(m)\ge R(j)(m/j)^\alpha\qquad\text{for every integer }m\ge j. \tag{1}
$$
In particular $R(j+1)=R(j)+1$. A record gives a bound even for the very next site. The definition places no upper limit on $m$.

**A finite test and a count.** For every integer $N\ge13$, at least $R(N)/16$ distinct $j\in[N,3N)$ satisfy (1) for $\alpha=1/2$. For any $j\ge13$, being such a record is equivalent to the finite list of comparisons
$$
 mR(j)^2\le jR(m)^2\qquad(j\le m<3j). \tag{2}
$$
For example, $R(19)=8$ and $64m\le19R(m)^2$ holds for every $m\ge19$. All three assertions are checked for the actual Roth number in Lean. [Finite test and count](RothFutureRecords.lean) · [Integer comparison](RothPowerRecords.lean) · [All-future example](RothRecordNineteen.lean) · [Exact initial value and record](RothNineteenUpper.lean)

**Larger exponents.** For every fixed $0<\alpha<1$, there are constants $B_\alpha$ and $c_\alpha>0$ such that every sufficiently large interval $[N,B_\alpha N)$ contains at least $c_\alpha R(N)$ records for exponent $\alpha$. Their total number up to $X$ is therefore $\Theta_\alpha(R(X))$. More quantitatively, index each jump by its rank, the value $k$ just before the jump. On long multiplicative intervals of ranks, the records for $\alpha$ occupy at least a fraction $1-\alpha-o(1)$ under logarithmic weighting, uniformly in the initial rank. The error and the weighting are specified below.

## Square-root growth

Put $f(n)=R(n)/\sqrt n$. Two copies separated by a gap give $R(3k-1)\ge 2R(k)$ for every positive $k$. For $m\ge3N$, put $k=\lfloor m/3\rfloor\ge N\ge13$. Then $81m\le256k$, so $8f(m)\ge9f(k)$. Iteration shows that the minimum $e(N)=\min_{m\ge N}f(m)$ is attained in $[N,3N)$. This proves the finite test. Also
$$
 e(3N)\ge(9/8)e(N),\qquad e(N)\ge R(N)/(2\sqrt N).
$$
If $j$ is not a record, a minimum from $j$ occurs strictly later and $e(j+1)=e(j)$. At a record, $e(j)=f(j)$ and $e(j+1)-e(j)\le 1/\sqrt j$ because the Roth number increases by at most one. Summing from $N$ to $3N-1$ proves the count. [Two-copy inequality](RothGrowth.lean)

For the numerical example, seven explicit free sets at lengths $19,20,25,30,36,43,51$ supply the required lower bounds at every length from 19 through 56. The kernel verifies every witness and propagates their bound to all future lengths. An exhaustive search at 19 proves the matching upper bound; its soundness follows by branching on whether the largest remaining point is present. An independent Python program enumerates all nine-element subsets at 19 and checks different-sized witnesses. [Independent checker](check_roth_records.py)

## A finite test for any rational exponent

Let $s\ge1$, $b=2s$, and $p=R(s)$. For $n\ge b$ and $m\ge bn$ put $k=\lfloor m/b\rfloor$. The digit construction yields $R(m)\ge pR(k)$ and $m\le(b+1)k$. Thus if $p\ge(b+1)^\alpha$ the minimum of $R(m)/m^\alpha$ over $m\ge n$ is attained in $[n,bn)$. At rational $\alpha=A/D$ the test uses only integer powers. The implication is proven in Lean with the finite certificate $(b+1)^A\le R(s)^D$. [Power test](RothPowerRecords.lean) · [Digit construction](RothHeight.lean)

Take $\kappa=p/(b+1)^\alpha>1$. The same minimum, now $e_\alpha(n)$, satisfies $e_\alpha(bN)\ge\kappa e_\alpha(N)$ and $e_\alpha(N)\ge R(N)/(bN)^\alpha$. Each of its increases at $j\ge N$ is supported on a record and has size at most $N^{-\alpha}$. Therefore $[N,bN)$ contains at least $(\kappa-1)R(N)/b^\alpha$ records. The choice $s=\lceil\exp(36/(1-\alpha)^2)\rceil$ suffices by $R(s)\ge s\exp(-4\sqrt{\log s})$. Indeed $(1-\alpha)\log s-4\sqrt{\log s}\ge12/(1-\alpha)>\log 3$ and $b+1\le3s$. For the cumulative count take $N=\lfloor X/b\rfloor$ and use $R(X)\le (b+1)R(N)$ for sufficiently large $X$, by partitioning into blocks of length $N$. Every record is at a jump, which gives the upper bound $R(X+1)$. [Behrend lower bound in mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Additive/AP/Three/Behrend.html#Behrend.roth_lower_bound)

## Logarithmic frequency among the jumps

Let $P(k)$ be the last $n$ with $R(n)=k$, defined for all $k\ge1$ because $R$ is unbounded with increments zero or one. Testing whether $P(k)$ is a record only requires comparison to $P(l)$ for $l\ge k$, the worst location on each subsequent plateau. Set
$$
 g(k)=\log k-\alpha\log P(k),\qquad E(k)=\min_{l\ge k} g(l).
$$
For integers $v\ge u\ge1$, write $z=v/u$. Two scale comparisons control the error uniformly in $u$:
$$
 \max\{1,z-1\}\le P(v)/P(u)<2(P(\lceil z\rceil)+1).
$$
The lower bound uses $v\le\lceil P(v)/P(u)\rceil u$ by partitioning. For the upper bound choose $s=P(\lceil z\rceil)+1$. Then $R(2sP(u))\ge R(s)u=(\lceil z\rceil+1)u>v$. The Behrend estimate applied at $P(k)$ implies $\log P(k)=\log k+O(1+\sqrt{\log k})$. These facts yield, for $h=\log(v/u)$,
$$
 g(v)-g(u)=(1-\alpha)h+O(1+\sqrt h).
$$
In particular the minimum defining $E(u)$ is attained and $0\le g(u)-E(u)\le C/(1-\alpha)$ for an absolute $C$. This last inequality follows by minimizing $(1-\alpha)h-C_1(1+\sqrt h)$ on $h\ge0$. Hence
$$
 E(v)-E(u)=(1-\alpha)\log(v/u)+O\!\left((1-\alpha)^{-1}+\sqrt{\log(v/u)}\right). \tag{3}
$$

An increment $E(k+1)-E(k)>0$ requires $g(k)=E(k)$ and hence a record at $P(k)$. At that rank the increment is at most $g(k+1)-g(k)\le\log(1+1/k)$. At other ranks it vanishes or obeys the same upper bound. Summing gives
$$
 \sum_{\substack{u\le k<v\\P(k)\ \mathrm{is\ a\ record}}}\log(1+1/k)
 \ \ge (1-\alpha)\log(v/u)-
 O\!\left((1-\alpha)^{-1}+\sqrt{\log(v/u)}\right).
$$
The total weight of all ranks in this interval is exactly $\log(v/u)$. In particular the lower proportion holds on every sufficiently long logarithmic interval, including intervals starting at arbitrarily large ranks. This argument for real exponents and frequency is a written proof. The square-root statements, the finite rational-exponent test, and the example at 19 are verified in Lean. These one-sided estimates on the actual extremal function leave its explicit asymptotic equivalent open. [Erdős problem 142](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/142.lean)
