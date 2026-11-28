# Exact defects at every displacement in extremal Roth sets

Let $R(n)$ be the largest cardinality of a subset of $[n]=\{0,\ldots,n-1\}$ containing no nonconstant three-term arithmetic progression. For a free set $A$ and $d>0$, let $\tau_A(d)$ be the minimum number of its points meeting every triple of **distinct** elements with $|x+z-2y|=d$. The designated $y$ may be outside the interval with endpoints $x,z$. All results below use absolute defects.

**Every displacement.** If $B\subseteq[n]$ is free and has no witness for $t,2t,4t$, then
$$
 7|B|\le 6R(n+2t)\qquad(t\ge1). \tag{1}
$$
Consequently, for $n\to\infty$, $|A|=(1-o(1))R(n)$ and **every** $1\le t\le H=o(n)$, at least one of the three exact values has $\tau_A(d)\ge(1/21-o(1))R(n)$. Such a value has at least $(1/63-o(1))R(n)$ witnesses on disjoint three-point supports. A maximal family of disjoint witnesses meets every further witness. The finite inequality (1) has been proved end to end in Lean for mathlib's `rothNumberNat`. [Formal proof](RothDyadicClusters.lean)

**Exceptional pairs of defects.** Let $A$ be an exact optimizer and fix $0<\gamma<1$. In the entire interval $1\le t\le n^{1-\gamma}$, at most $\log_{3/2}(n/R(n))+o(1)=O(\sqrt{\log n})$ steps have
$$
 \tau_A(t)+\tau_A(2t)\le R(n)^3/n^2. \tag{2}
$$
Outside these exceptions at least one of the two defects has more than $R(n)^3/(6n^2)=n^{1-o(1)}$ witnesses on pairwise disjoint triples. Moreover, $1-o(1)$ of the points of $A$ form disjoint binary cubes with all exceptional steps as their common directions. In an arithmetic progression of $L$ candidate steps there are at most $\log_3 L+O(\log\log(3L))$ exceptions. [Proof and constants](RothPairDirections.md)

## An inequality for two target defects

Write $P_t(B)=|\{b\in B:b+t\in B\}|$. For a free $B$ with neither $t$ nor $2t$ witnessed by three distinct points,
$$
 4|B|\le 3R(n+t)+2P_t(B). \tag{3}
$$
Consider $B\cup(B+t)$. An arithmetic progression in the union projects to inputs of signed defect $0,\pm t,\pm2t$, so at least two inputs agree. If exactly two agree, the two distinct values differ by $t/2,t$ or $2t$. A nontrivial progression cannot come from just one input. To find a large free subset it therefore suffices to make independent choices on the connected components of $B$ for these three pair distances. Distinct components have disjoint outputs: coincident outputs would require original points equal or a distance $t$ apart.

Inside one component with minimum $a$, use the integer coordinate $j=2(x-a)/t$. Connecting edges have lengths $1,2,4$. A triple on distinct coordinates cannot have signed defect $0,\pm2,\pm4$. Starting with $\{0\}$ and adjoining one accessible coordinate at a time gives precisely the seven possibilities in the first column below. This list can be checked without an input-size cutoff. From each listed set, every nonnegative new neighbor is at most $9+4=13$. The finite check tests every candidate through 13 and verifies that an admissible extension belongs to the list. Induction then covers each full connected component. At odd $t$ all the indices in a component are even. The same verification applies.

In this coordinate $B\cup(B+t)$ on a component has support $C\cup(C+2)$. The following choices have no nonconstant progression.

| Component $C$ | Selected output indices |
| --- | --- |
| $0$ | $0,2$ |
| $0,1$ | $0,1,3$ |
| $0,2$ | $0,2$ |
| $0,4$ | $0,2,6$ |
| $0,1,5$ | $0,1,3,7$ |
| $0,4,5$ | $0,2,5,6$ |
| $0,4,5,9$ | $0,2,5,6,9,11$ |

Each row provides at least $4|C|/3$ outputs except for $C=\{0,2\}$, a single pair at distance $t$. Subtracting $2/3$ for that pair gives the valid row bound. Adding the contributions, the selected outputs fit in $[n+t]$, proving (3).

If $B$ avoids all three target defects, apply (3) at $t$ and at $2t$. The edges of lengths $t$ and $2t$ together form a matching in $B$. Two edges meeting at a vertex would give, on its $t$-spaced row, three ordered points. If the vertex is between its neighbors, the gaps are each $t$ or $2t$ and differ by at most $t$. If the two neighbors are on the same side, the ordered points have gaps $t,t$. Both possibilities contradict ordinary freeness or avoidance of defect $t$. Thus $2(P_t(B)+P_{2t}(B))\le |B|$. Adding (3) at the two steps yields (1). For the corollary remove a minimum cover for each of $t,2t,4t$. The elementary digit inequality $R(2uv)\ge R(u)R(v)$ implies $R(2H)=o(R(n))$ when $H=o(n)$ by taking $u=2H$ and $v=\lfloor n/(4H)\rfloor$. Subadditivity controls $R(n+2t)$ uniformly. [Digit construction](RothHeight.lean)

## Compression with two defects and dilation with one

Let $W_2(n,t)$ be the largest size of a free set with no three-distinct-point witness for $t$ or $2t$. Let $W_1(n,t)$ impose only the defect $t$. For all positive integers $n,t$,
$$
 W_2(n,t)\le R\left(\left\lceil \frac{4(n-1)+6t}{5}\right\rceil\right),\qquad
 \frac32 W_1(n,t)\le R(2(n-1+t)). \tag{4}
$$
In particular on lengths where $R(\lceil4n/5\rceil)=(4/5+o(1))R(n)$, every $t=o(n)$ satisfies $\tau_A(t)+\tau_A(2t)\ge(1/5-o(1))R(n)$ for near-optimal $A$. Subadditivity and the digit bound absorb the $O(t+1)$ boundary sites. These lengths include a set of logarithmic density one by the earlier variation argument. Likewise, on any sequence with $R(2n)\le(3/2-\epsilon)R(n)$ for fixed $\epsilon>0$, every $t=o(n)$ has $\tau_A(t)\ge(2\epsilon/3-o(1))R(n)$. The latter statement is conditional on the indicated doubling behavior. [Variation on logarithmically typical lengths](RothPunctures.md)

Here is the selection proving (4). For a slope $\lambda>0$, allow outputs $Y\equiv x\pmod t$ satisfying
$$
  \lambda x+c\le Y<\lambda x+c+v\lambda t.
$$
For two excluded defects take $v=3/2$ and $\lambda=4/5$. For one excluded defect take $v=1$ and $\lambda=2$. Given a progression of outputs, the input defect is a multiple of $t$ with absolute value strictly less than $2vt$. Hence it vanishes or is one of the excluded signed defects. Three distinct inputs are impossible. For two distinct inputs the pair distances possible in the two-defect case are $t/2,t,2t$. In the one-defect case they are $t/2,t$. Coinciding outputs from different inputs would require the same residue and input distance $<vt$, so they belong to the same component as well.

For one defect the normalized edges have lengths $1,2$ and the forbidden signed defects are $0,\pm2$ on distinct coordinates. The component shapes are $\{0\},\{0,1\},\{0,2\},\{0,1,3\},\{0,2,3\},\{0,2,3,5\}$. Checking all single-neighbor extensions through $5+2=7$ proves exhaustiveness as above.

Write $u=2(Y-a)/t$ for outputs near a component based at $a$. The candidates obey $u\equiv j\pmod2$ and $\lambda j+h\le u<\lambda j+h+2v\lambda$ with $h=2((\lambda-1)a+c)/t$. Shifting $h$ by 2 translates the whole local problem. For $\lambda=p/q$ and integer $2vp$ the phase reduces to $h'=\lceil qh\rceil\bmod 2q$ in the integer comparison
$$
 pj+h'\le qu<pj+h'+2vp.
$$
An additive period of $2q$ shifts $u$ by 2. For $4/5$, all ten phases of each of the seven shapes admit at least $|C|$ free outputs. For slope 2 the combined output counts at the two phases are at least $3|C|$ on each one-defect shape. Choosing $c$ uniformly on $[0,t)$ gives equal weight to both phases, even when different components receive different phase offsets. Some single choice of $c$ therefore retains at least $3|B|/2$ points. The containing half-open interval has length $\lambda(n-1+vt)$, giving both bounds in (4). All 82 finite phase selections are kernel-checked. [Phase certificates](RothClusterWindows.lean)

For comparison, $W_1(n,t)\ge R(n)/4$ at every $n,t$. Intersect an optimal free set with a random translate of $\lceil t/2\rceil$ consecutive residues modulo $2t$. Defects in those residues cannot equal $t$ modulo $2t$. For odd $t$, taking the better parity class gives $W_1(n,t)\ge R(n)/2$. Formula (4) still leaves the asymptotic size for a single prescribed defect undetermined in general.

## Verification scope

[RothDyadicClusters.lean](RothDyadicClusters.lean) proves (1) and (3) for the actual finite Roth number, including residue splitting, the exhaustive component argument, gluing, and counting. [RothClusterWindows.lean](RothClusterWindows.lean) checks the extra finite cases used in the written proof of (4). Compile the first file before the second in the repository's Lean and mathlib environment. [RothClusterCovers.lean](RothClusterCovers.lean) also proves the finite estimates for arbitrary covers of the individual defects, importing the earlier [definition of covers](RothExactDefects.lean). Run `python3 check_roth_clusters.py` for independent enumeration of the templates, point selections and small interval instances. These structural restrictions do not give the explicit asymptotic for $R(n)$ required by [Erdős problem 142](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/142.lean).
