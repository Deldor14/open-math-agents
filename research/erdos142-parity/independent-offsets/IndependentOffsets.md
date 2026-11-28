# Small independent shifts of a near-extremal progression-free set

Let R(n) be the size of a largest three-term-progression-free subset of
{0,…,n−1}. Let A be any progression-free subset of that interval, t≥1, and

    D = max(0, |A| − 6R(n+2t)/7),      p = 1−1/√3,      π = p³.

Independently at each point of A add 0, t or 2t with respective
probabilities p, 1−2p, p. Let X be the **set** of images, writing
α(X) for the largest size of a progression-free subset of X.
With probability at least 1−exp(−πD/24), both bounds hold:

    α(X) ≤ |A| − πD/6,           |X|−α(X) ≥ πD/18.

Also, the probability that X itself is progression-free is at most
(1−π)^(D/3). These bounds include the case where several points land on
the same site. When |A|=(1−o(1))R(n), the first bound excludes retaining
more than (1−π/42+o(1))R(n) points, uniformly for 1≤t≤H=o(n).
The assertion concerns this random modification of an extremal set.
It supplies no asymptotic equivalent for R(n).

## Matching the exact defects

We use the coordinated [dyadic-defect result of Deldor14](https://github.com/Deldor14/open-math-agents/blob/dcf3f99d3327bbe45920a936c08ddf8de3943634/research/erdos142-hinge/RothDyadicClusters.md). If a free
B⊆[n] contains no three **distinct** x,y,z with
|x+z−2y| in {t,2t,4t}, then 7|B|≤6R(n+2t). The designated y need
not be between the other two inputs.

Take a maximal family of witnesses with disjoint three-point supports.
If its size is L, deleting the 3L points leaves such a B, so L≥D/3.
Fix this family before sampling the offsets.

For a witness with shifts it,jt,kt, the corrected sites are in
progression when (i+k−2j)t cancels its signed defect. If those sites
all coincide, the three labels must be distinct because the original
sites are distinct. But for a permutation of 0,1,2 the expression
i+k−2j is 0 or ±3. Thus every correction counted here makes a
nonconstant progression. The Lean file verifies this implication.

For either sign, put b=1−2p. The correction probabilities are

| Absolute defect | Probability |
|---|---|
| t | 2pb²+2bp² |
| 2t | p²b+2p³+pb² |
| 4t | p³ |

At our choice of p the first and third entries coincide, while the
second is larger. Thus each witness succeeds with probability at least π.
Since inputs were chosen disjointly, the successes are independent.
If S counts them, E[2^(−S)]≤(1−π/2)^L. Markov's inequality gives
P(S≤πL/2)≤exp(−πL(1−log 2)/2)≤exp(−πL/8).

For any free subset Y of X, every successful triple has an input whose
image is absent from Y. Distinct successes use distinct inputs and
therefore |Y|≤|A|−S. Every missing image can account for at most three
of these inputs, as it has at most three possible preimages. Consequently
|X|−|Y|≥S/3. The claimed bounds follow; if X is free, S=0.

## Uniformity and a finite range

The standard no-carry construction gives R((2m−1)v)≥R(m)R(v), and
R(n+s)≤R(n)+R(s) by splitting the interval. If H=o(n), choose m→∞
with (2m−1)2H≤n. Then R(2H)/R(n)≤1/R(m)=o(1), uniformly giving
R(n+2t)≤(1+o(1))R(n) in this range.

There is a finite version with no limiting assumptions. Three ternary
digits chosen from {0,1} give eight free points on fourteen sites, so
R(54t)≥8 R(2t). If n≥54t and |A|≥(1−η)R(n), this implies
D≥(1/28−η)R(n). In particular a positive fraction of points is lost
with exponentially high probability for every such t if η<1/28 is fixed.

## Optimal common probability for a single witness

The constant π is the largest possible worst-case success probability
over all laws on {0,t,2t} used independently with the same law at each
site, when either sign of t,2t,4t must be correctable. This optimality
concerns only the single-witness calculation.

Write the masses as u+d, v, u−d with v=1−2u. By interchanging the
extremes take 0≤d≤u. The smaller of the two probabilities at ±4t is
(u−d)(u²−d²)≤u³. If u≤1/3 this already lies below π. For u≥1/3
the smaller probability at ±t is

    2v (u²+uv+d²−(2u−v)d) ≤ 2u(1−2u)(1−u),

because 2u−v=4u−1≥u≥d. The right side decreases on [1/3,1/2]:
both u(1−2u) and 1−u are nonnegative and decreasing there.
The other bound u³ increases. The two coincide at u=1−1/√3,
and the symmetric law actually attains the bound.
