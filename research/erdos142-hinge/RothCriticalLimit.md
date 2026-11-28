# An explicit limit at the square-root sampling threshold

Retain each site of $[1,n]$ independently with probability $1/\sqrt n$. Write $\alpha_3(S)$ for the largest size of a three-term-progression-free subset of the retained sites. Then
$$
 \alpha_3(S)/\sqrt n\ \longrightarrow\ f
 \quad\hbox{in probability and in mean},\qquad
 0.865100\ \le f\le\ 0.865874.                                    \tag{1}
$$
The same limit holds for a uniform sample of $\lfloor\sqrt n\rfloor$ sites. The number $f$ is defined exactly by (3) and (7) below. The numerical enclosure uses integer arithmetic. It concerns a random subset of a growing interval; the asymptotic size of a maximum progression-free subset of the entire interval in Erdős 142 remains open.

## The integral equation

Fix $k\ge3$, $\lambda>0$, and take $p=(\lambda/n)^{1/(k-1)}$ for sufficiently large $n$. For $0\le x\le1$ and $0\le i<k$, let $h_i(x)$ be the maximum length parameter $s\ge0$ such that $0\le x-is$ and $x+(k-1-i)s\le1$. Write $h(x)=\sum_i h_i(x)$, $H=\max h$. For a function $q:[0,1]\to[0,1]$ define
$$
 K(q)(x)=\sum_{i=0}^{k-1}\int_0^{h_i(x)}
          \prod_{j\ne i}q(x+(j-i)s)\,ds .
$$
If
$$
                   \lambda(k-1)H<e,                               \tag{2}
$$
there is a unique continuous solution
$$
                        q_\lambda(x)=\exp(-\lambda K(q_\lambda)(x)). \tag{3}
$$
For this range the limiting value of $\alpha_k(S_p)/(np)$ in probability and in mean is
$$
 F_k(\lambda)=\int_0^1\int_0^1 q_{\lambda t^{k-1}}(x)\,dx\,dt .     \tag{4}
$$
Here $q_0=1$. For $k=3$, $h(x)=1/2+\min(x,1-x)$ and $H=1$, so (2) holds throughout $0<\lambda<e/2$, including $\lambda=1$. The weighted argument below extends the three-term formulas to $0<\lambda<e/1.563804$. The [all-length comparison](RothEffectiveLength.md) gives order estimates for every $\lambda$; this note identifies an actual limit in (2). The local optimization argument follows the general idea of analyzing increments on tree neighborhoods. For related results for sparse random graphs see [Gamarnik, Nowicki and Świrszcz](https://arxiv.org/abs/math/0309441). The edges here come from arithmetic relations on integer sites.

## The rooted arithmetic neighborhood

Force one site chosen uniformly in $[1,n]$ to be present, and retain the other sites independently with probability $p$. Make a hyperedge for every surviving nonconstant $k$-term progression. Mark each site by its coordinate divided by $n$. To a fixed depth, counting one generation per hyperedge, the rooted neighborhood converges to the following random tree of hyperedges. The root is uniform on $[0,1]$. From a vertex of type $x$, independently for each position $i$, generate Poisson points of intensity $\lambda\,ds$ on $[0,h_i(x)]$. Each point $s$ gives one edge to the $k-1$ children of types $x+(j-i)s$, $j\ne i$. Use independent point processes at new vertices. The parent edge is excluded from the offspring.

Here are details because the arithmetic host has many deterministic relations. Fix a finite rooted tree shape to depth $d$, with the child slots labelled by their positions in the increasing progression. Order offspring edges of a vertex by anchor position $i$ and then by their positive step. A tree with $a$ edges has $1+(k-1)a$ vertices, parametrized by the initial integer site and $a$ integer steps. Restrict these parameters by the endpoint bounds, the specified ordering and, optionally, fixed interval constraints on the scaled marks with null boundary. The normalized sums over these lattice parameters are Riemann sums on the corresponding bounded polytopes. Apart from a finite union of proper affine hyperplanes there are no coincident vertices, repeated steps at the same anchor position, or further progressions wholly among the displayed vertices. For the last assertion, attach edges in a parent-before-child order and consider the most recently introduced step that occurs in a putative extra progression. Its coefficients in the displayed sites are zero on older vertices and $j-i$ at the new leaves. A progression identity would force these coefficients to be an arithmetic progression. A nonzero coefficient occurs only once. A nonconstant progression of coefficients must use the full list of $k$ consecutive coefficients in forward or reverse order. Its zero-coefficient site must then be the original attachment site, from the coordinate equation. This gives exactly the edge just attached. A coefficient list consisting only of zeros reduces to older vertices. Distinct coordinate forms likewise remain distinct after an attachment. Discarding the proper hyperplanes costs $O_{k,d,\mathrm{shape}}(n^{a})$ parameter tuples.

Condition on occupation of the displayed vertices for a generic tuple. To recognize the neighborhood, exclude additional edges incident with any vertex at depths strictly less than $d$. Edges using at least two displayed vertices and at least one fresh site give total conditional probability $O_{k,\mathrm{shape}}(p)$, because two sites determine only boundedly many progressions. For candidate edges using exactly one displayed vertex, let $m_n$ be their number. Then
$$
 m_n=n\sum_{v\ {\rm internal}} h(v/n)+O_{k,\mathrm{shape}}(1).
$$
Each event requires $k-1$ fresh sites. Different candidates sometimes require the same fresh set. There are only boundedly many such duplications. Indeed for two distinct displayed anchors the smallest and largest fresh coordinates determine each anchor as an affine combination with coefficients from a fixed finite list; different anchors require different coefficients. The two anchor values then determine both fresh extremes, and the remaining sites have boundedly many choices. For a single anchor identical fresh sites give the same edge.

After removing duplicates, each event shares fresh sites with at most $O_{k,\mathrm{shape}}(1)$ others, since an anchor and a fresh coordinate determine boundedly many progressions. Their count of occurrences has zero-event probability
$$
           \exp(-m_n p^{k-1})+o(1) .                               \tag{5}
$$
For an elementary verification, in the factorial moment of any fixed order group selected candidates into connected components by shared fresh sites. Each singleton contributes $O(np^{k-1})=O(1)$. A connected component of at least two candidates has $O(n)$ placements and uses at least $k$ fresh sites, contributing $O(np^k)=o(1)$. Distinct components have disjoint fresh sites. The all-singleton terms give $(m_n p^{k-1})^j+o(1)$ at order $j$, since the tuples lost by requiring disjointness are $O_j(n^{j-1})$. Bonferroni bounds for the zero event, then the exponential series with bounded parameter, prove (5) uniformly in the displayed generic tuples.

The probability contribution of each such tuple, including the choice of root, is $n^{-1}p^{(k-1)a}$ times (5) plus an error $o(n^{-1}p^{(k-1)a})$. Nongeneric embeddings with all vertices distinct have total probability $O(1/n)$. The Riemann sum therefore gives the probability of precisely the stated tree shape in the independent Poisson construction, including its mark constraints. There is no factorial to insert for the already ordered steps. Tuples with coincident vertices were never counted as embeddings of this tree. At finite depth the Poisson construction is almost surely finite. The probabilities of its countably many finite shapes sum to one, so convergence on each tree shape leaves vanishing probability for non-tree neighborhoods or mass escaping to unbounded shapes.

## The gain from adding a site

Compare the optima with the root available and with it omitted. The gain is zero or one. In a tree neighborhood, fix any feasible assignments on its boundary and exterior. At an internal vertex compare its best score when included and when excluded. For an incident child edge, including the parent forces at least one child to be excluded. Excluding the parent leaves that edge unconstrained. This costs zero if some child has a maximizing choice excluding it, and otherwise costs at least one. Different child edges separate into disjoint subtrees conditional on the boundary. Thus the internal vertex has a strictly positive gain from inclusion precisely when **no** child edge has every child strictly preferring inclusion. In that case the gain is one, as the vertex itself contributes one. Boundary vertices fixed present or absent have messages one or zero respectively. If a forced assignment makes including an internal vertex infeasible, its message is zero; excluding an internal vertex is always feasible with a feasible exterior, by deleting its free internal descendants. Equivalently the edge cost may be infinite just above a fixed boundary.

The recursion on messages reverses the pointwise order at every generation. The two extreme boundary conditions (all messages zero or all one) bracket the root gain for every feasible exterior assignment. They serve as formal message bounds even if the exterior disallows one of those extreme assignments. Taking maxima over the exterior preserves the same two bounds on the difference in the global optima. In the limiting tree, independent children have positive messages with the probabilities of the preceding iterate. Poisson thinning therefore gives the two iterates of $q\mapsto \exp(-\lambda K(q))$, starting from zero and one.

To prove convergence, use the variable $g=\sqrt{-\log q}$. After one update the probabilities are bounded below by $\exp(-\lambda H)$, including when the initial probability was zero. The new $g$ equals the square root of $\lambda\int e^{-\sum_j g_j^2}\,d\nu_x$, where $\nu_x$ sums the step measures from the $k$ anchor positions and has mass $h(x)$. Differentiate along the line between two bounded input functions. Cauchy–Schwarz bounds the square of the pointwise directional derivative by
$$
 \lambda\|\Delta g\|_\infty^2
 \int e^{-\sum_j g_j^2}\Big(\sum_j|g_j|\Big)^2\,d\nu_x
 \ \le\ \lambda(k-1)H e^{-1}\|\Delta g\|_\infty^2 .
$$
The last step uses $u e^{-u}\le1/e$. Differentiation is legitimate on bounded functions since $h(x)\ge1/(k-1)$ and the integrand remains positive. The map preserves continuous functions. Under (2) it is a contraction, giving (3) and convergence of both boundary bounds. Local convergence at each fixed depth followed by this contraction shows that the expected root gain tends to $\int q_\lambda(x)\,dx$.

For finite $n$, differentiation of the Bernoulli expectation is the sum over sites of these expected add-one gains, by expanding the product measure in each coordinate. Integrate from retention zero to $p$. At retention $tp$, for fixed $t>0$, the intensity parameter is $\lambda t^{k-1}$ and the same argument applies. Gains are bounded by one, so dominated convergence gives (4) for the normalized expectation. The exposure martingale for the maximum has conditional variance per site at most $p(1-p)$, since the conditional score changes by at most one when that site changes. Thus the normalized variance is at most $1/(np)$, proving the asserted convergence. Coupling to a uniform sample of $\lfloor np\rfloor$ by a random permutation costs at most the difference of sample sizes, of expectation $O(\sqrt{np}+1)$.

## A larger uniqueness interval from the spatial types

The independent verifier of this project suggested keeping the individual perturbations in the contraction estimate. In the square-root logarithmic variable let $\Phi$ denote the update. Write $L$ for the positive operator that sums the integrals of the individual child values over every allowed edge through the parent. Cauchy–Schwarz in the step variable, then in the finite child list, gives
$$
 |D\Phi(g)h(x)|^2\le \lambda\int e^{-\sum_jg_j^2}(\sum_jg_jh_j)^2\,d\nu_x
       \le (\lambda/e) L(|h|^2)(x).
$$
Indeed $(\sum_jg_jh_j)^2\le(\sum_jg_j^2)(\sum_j h_j^2)$. For any positive continuous $w$ with $Lw\le\kappa w$, the map contracts in $\sup_x |h(x)|/\sqrt{w(x)}$ whenever $\lambda\kappa<e$. This norm is equivalent to the ordinary supremum norm and all boundary and differentiation arguments above apply.

For three terms, integration over the endpoint and midpoint roles yields
$$
 Lw(x)=\tfrac12\int_0^1w + \int_{x/2}^{(1+x)/2}w
      + \int_{\max(0,2x-1)}^{\min(2x,1)}w .
$$
The verifier's explicit first choice $w=1/2+\min(x,1-x)$ gives $Lw\le13w/8$. On $[0,1/4]$ its image is $(3+5x+7x^2)/4$, and on $[1/4,1/2]$ it is $(2+13x-9x^2)/4$, with the rest given by reflection. In the first half-cell the slack is concave and positive at both endpoints. In the second it is $(36x^2-26x+5)/16>0$.

[An exact rational certificate](check_roth_weighted_contraction.py) gives a positive piecewise linear $w$ on 128 equal cells with
$$
             1.563684\,w\le Lw\le 1.563804\,w .
$$
It constructs the integer nodes by sixteen normalized iterations, with rounding used only to select a witness. On each of 256 half-cells the integral formula for $Lw$ is exactly quadratic. A quadratic with endpoint values $a,c$ and midpoint value $b$ has Bernstein coefficients $a,2b-(a+c)/2,c$. A linear denominator has Bernstein coefficients equal to its values at the two endpoints and midpoint. The ratios of corresponding coefficients, bounded by rational arithmetic on all half-cells, enclose the function ratio throughout. Thus (3), (4) and (7) hold throughout $0<\lambda<e/1.563804$, in particular at $\lambda=1.738$. Also every positive continuous weight $z$ with $Lz\le\kappa z$ has $\kappa\ge1.563684$. Indeed $w\le C z$ and iteration bounds $1.563684^m w\le L^m w\le C\kappa^m z$. This last lower bound concerns this sufficient contraction test only.

## Evaluating the limit at one intensity

Let $A(\lambda)=\int q_\lambda(x)\,dx$ and
$$
 B(\lambda)=\int_{0\le y\le1,\ 0\le s\le(1-y)/(k-1)}
                     \prod_{j=0}^{k-1}q_\lambda(y+js)\,dy\,ds .
$$
The fixed point is differentiable in $\lambda$ in any compact subinterval of the strict contraction range with positive left endpoint. For clarity, the map is continuously Fréchet differentiable in $g$ and in the positive parameter $\lambda$ (the integrals have uniformly bounded smooth integrands on bounded sets and a square root bounded away from zero there for $\lambda>0$). The linearization in $g$ has norm less than one, so $1-D_g$ has a convergent Neumann-series inverse. This justifies differentiating the fixed point, or follows directly by taking difference quotients.

Differentiate (3) and integrate over the anchor. Counting each edge at all its $k$ anchor positions yields
$$
 A'=-kB-\lambda(k-1)B'.                                           \tag{6}
$$
In the term where a factor $q$ is differentiated inside $K$, each differentiated edge position can occur with each of its $k-1$ other positions as anchor, giving the second coefficient. The change of variables $x=y+is$ has unit Jacobian. Put $J=A+(k-1)\lambda B$. Then $J'=-B$ and $J+(k-1)\lambda J'=A$. Integrating the derivative of $tJ(\lambda t^{k-1})$ from zero to one identifies $J$ with (4), since $J$ remains bounded near zero. Also $\int q_\lambda(-\log q_\lambda)=k\lambda B$. Hence the convenient single-intensity formula
$$
 F_k(\lambda)=\int_0^1 q_\lambda(x)
          \left(1-\frac{k-1}{k}\log q_\lambda(x)\right)\,dx .       \tag{7}
$$
As a check at low intensity, $q_\lambda=1-\lambda h+O_k(\lambda^2)$ uniformly by (3), so $B(\lambda)=1/(2(k-1))-\lambda\int h(x)^2 dx+O_k(\lambda^2)$. From $J'=-B$ this gives $F_3(\lambda)=1-\lambda/4+7\lambda^2/24+O(\lambda^3)$.

## Integer enclosure at three terms

[The standalone checker](check_roth_critical_limit.cpp) encloses the continuous fixed point on each of 4,096 equal spatial cells. Start with bounds $0,1$, in units of $10^{-6}$. At each of 40 updates cover the step variable by cells of the same width. Include a full step cell in the lower integral only when it is admissible for every parent coordinate in that spatial cell; include it in the upper integral whenever it can be admissible. For a child offset $l=j-i$, a parent in cell $a$ and step in cell $b$ place the child in cells numbered from $a+lb+\min(0,l)$ through $a+lb+\max(0,l)$, after clipping to the domain. Step endpoints of measure zero do not affect either integral. Reflection is valid because (3) is invariant under $x\mapsto1-x$ and the fixed point is unique.

Round each exponential outward using $(1-x/m)^m\le e^{-x}\le(1+x/m)^{-m}$ with $m=16384$, repeated squaring, and internal denominator $10^{12}$. Intersect with the previous enclosure. The integrand in (7) is increasing in $q$ on $(0,1]$. For its logarithm use the positive series $-\log q=2\sum_{j\ge0}t^{2j+1}/(2j+1)$, $t=(1-q)/(1+q)$, with an outward geometric remainder. The code verifies $t^2\le1/2$ for the inputs to this calculation. All products involving the finer denominator are evaluated in signed 128-bit integers; the largest one, in the exponential reciprocal, is below $10^{33}$. The output is the interval in (1), in millionths. Build with a C++17 compiler supporting this integer type.

[Six finite Lean lemmas](RothCriticalLimit.lean) verify the least child-omission cost for an edge, the zero-or-one root rule from edge penalties, the two pointwise contraction integrand bounds, the cancellation in (6), and the three-term anchor bound. [A separate finite checker](check_roth_tree_gain.py) compares the message recursion with exhaustive optima at fixed boundary assignments. The convergence of the arithmetic neighborhood, the continuum contraction and the passage to the limit have written proofs. The estimate above the uniqueness range, including the behavior needed to determine the large-$b$ density in [the deterministic comparison](RothEffectiveLength.md), remains open.
