# The information retained by a single degree in sparse interval samples

Let R(n)=r₃(n), δ(t)=R(⌈t⌉)/⌈t⌉ and D(t)=−log δ(t). In the continuous interval progression tree with intensity parameter d, a uniform root has type x∈[0,1], invisible to the selection rule. Every vertex of degree n accepts itself as a candidate independently with probability g(n), using its own uniform mark. Delete every candidate belonging to a triple of candidates. Let G(d) be the supremum of the root survival probability over all sequences 0≤g(n)≤1. Let G₀(d) restrict g to indicators of sets of integers. The supremum involves neither integer extremal numbers nor any search over multivariate local rules.

For all sufficiently large d, with absolute constants,

    c d^(−1/4) δ(√d) exp{−D(√log d)−O(1+√log log log d)}
       ≤ G₀(d) ≤ G(d) ≤ C d^(−1/4) δ(√d).                                  (1)

In particular for either supremum G*,

    −log(√N G*(N²)) = log(N/R(N)) + O(1+√log log N).

This follows from (1) and Behrend. The error is lower order than log(N/R(N)) by the upper bound on R of [Raghavan, Theorem 1.4](https://arxiv.org/html/2603.27045v3#S1). The polynomial factor d^(−1/4) shows the cost of using only a single degree before deletion. A candidate rule of radius three can obtain order δ(d) after deletion. [Four local steps](FourRoundRecovery.md)

## An exact scalar formula

At type x the incident edge count is Poisson of mean μ(x)=d(1−|x−1/2|). Write Pλg for the expectation of g(Poisson(λ)), F(x)=Pμ(x)[g(1+·)], zero outside [0,1]. At each vertex on a specified incident triple, the degree includes this one edge. The other incident counts are independent Poisson processes in the distinct descendant subtrees. Define the positive-spacing hazard

    L_F(x) = Σ_(j=0)² ∫_(h>0) ∏_(i≠j) F(x+(i−j)h) dh,     H(x)=d L_F(x).

An incident root edge is bad if its other two vertices are candidates. By independent thinning of marked Poisson processes, the numbers of bad and other incident edges are independent Poisson variables of means H and μ−H. Conditional on the absence of bad edges the root degree is the latter variable. Thus the exact objective is

    I_d(g) = ∫₀¹ exp(−H(x)) P_(μ(x)−H(x)) g dx.                             (2)

The rule is well-defined on the unordered hypergraph. Its finite sampled-interval version has exactly the same local limit at fixed d. Under d→∞ with log d=o(log N), uniform errors for this degree observable are o(d^(−A)) for each fixed A. Indeed the typed-tree comparison costs O(N^(−1/20)) at radius two; rounding the continuum types and steps in those two levels costs O((1+d)^3/N) by the expected number of atoms near a cutoff. These bounds are independent of g. [Coupling and conventions](IntervalLocalRecovery.md)

## A one-sided smoothing bound for every acceptance rule

For λ>0 the total variation distance between Poisson(λ) and its unit translate equals E|Z−λ|/(2λ)≤1/(2√λ), by taking the ratio of successive point masses. Add an independent Poisson(H) and then one unit to the first variable of mean μ−H. The shift bound for each integer displacement and the triangle inequality show that the distance to 1+Poisson(μ) is at most (H+1)/(2√(μ−H)). For H≤μ/2 this costs O(d⁻¹ᐟ²) after multiplication by exp(−H). For H>μ/2 the entire integrand is at most exp(−d/4). Hence

    I_d(g) ≤ ∫ F exp(−dL_F) + O(d⁻¹ᐟ²).

For any weight sequence 0≤v≤1 and positive mean μ≥1, a single sign σ∈{−1,1} satisfies

    P_(μ exp(σz)) v ≥ exp(−1) Pμ v      for every 0≤z≤1/√μ.

In the Poisson series the ratio of the n-th masses is exp((n−μ)σz−μ(exp(σz)−1−σz)). Choose the sign of E[v(Z)(Z−μ)]. The inequality exp(u)≥1+u after summation, and exp(w)−1−w≤w² for |w|≤1, prove the assertion including zero weights. [Lean proof for the full infinite series](PoissonOneSided.lean)

Apply this with v(n)=g(n+1). Omit a set of measure O(d⁻¹ᐟ²) around 0, 1/2 and 1. At every remaining x the mean is affine with slope ±d on a neighborhood of radius c/√d. One can move to one side by every distance up to c/√d, toward the good sign in the mean coordinate. Every new mean then has logarithmic displacement at most 1/√μ by choosing c small uniformly in d/2≤μ≤d. With x as an endpoint of each progression of spacing up to c/(2√d) on this side, we obtain L_F(x)≥c'F(x)²/√d.

Set a=√2 d^(−1/4), G₁=min(F,a). The last bound gives F exp(−dL_F/2)≤C G₁ there, and L_F≥L_(G₁)=a²L_(G₁/a). Integrating over the whole interval gives

    I_d(g) ≤ C a ∫ (G₁/a) exp(−√d L_(G₁/a)) + O(d⁻¹ᐟ²)
           ≤ C' d^(−1/4) δ(√d) + O(d⁻¹ᐟ²)

by the unrestricted [affine-sampling survival inequality](VariationSurvival.md). The last error is absorbed by Behrend or by iterating the ordinary ternary {0,1} construction. This proves the upper bound uniformly in g.

## Deterministic degrees despite Gaussian fluctuations

Set Q=⌊√d⌋, m=⌊Q/20⌋, L=⌈K√(d/Q)⌉. The large absolute constant K is chosen below. For a free B⊂[0,m) put t_b=0.22+b/Q. Select the integer degrees n that are multiples of L and satisfy |1−n/d−t_b|≤1/(12Q) for some b∈B. This single set of degrees is the same at every vertex.

Each window is disjoint and contains between c√d/L and C√d/L multiples of L for d large. For any x with ||x−1/2|−t_b|≤1/(24Q) the root candidate probability is at least c/L. In fact each degree in that window differs from μ(x) by O(√d), so its probability is at least c/√d by Stirling. The unconditional candidate probability is consequently ≥c|B|/(QL).

There are absolute C,κ>0 for which the Palm candidate probability satisfies

    F(x) ≤ (C/L) Σ_(b∈B, σ=±1) exp(−κQ²[x−(1/2+σ t_b)]²).

To see this, the allowed n lie in [0.6d,0.9d] and the Poisson mean lies in [d/2,d]. Stirling and Taylor's theorem for u log(u/μ)−u+μ give the upper mass bound C d⁻¹ᐟ² exp(−c(n−μ)²/d), also for n−1. The window width and the shift by one are absorbed by decreasing the Gaussian exponent and increasing its constant. Summing over multiples proves the display with constants independent of K for all sufficiently large d (the cutoff may depend on K).

The probability lost in deletion is at most the expected number of fully candidate edges incident at the root. In the Palm law of each specified triple all three endpoint candidate decisions are independent conditional on types, with probabilities F at their types. Thus the loss is at most d∫F L_F. For any three centers u,v,w,

    ∫_(ℝ²) exp(−κQ²[(x−u)²+(x+h−v)²+(x+2h−w)²]) dx dh
      = Cκ Q⁻² exp(−κ Q²(u−2v+w)²/6).

This follows by orthogonally projecting the center vector onto the complement of (1,1,1),(0,1,2), which is spanned by (1,−2,1). Integrating over positive h and the supported interval can only decrease the integral. Equal signs in the three centers give exactly the integer defect b₁−2b₂+b₃ up to sign after multiplication by Q. Mixed signs give |u−2v+w|≥0.39 since all t_b belong to [0.22,0.27]. There are O(Q³) such terms. Choose B by the [Gaussian defect theorem](GaussianDefects.md) for parameter κ/6. The resulting total loss is bounded by

    C d (W_(κ/6)(B)+Q³ exp(−cQ²))/(Q² L³) ≤ C' d |B|/(Q² L³).

Now take K large enough that C'd/(QL²)≤c/2, where c is the preceding candidate lower constant. The surviving probability is ≥c|B|/(2QL). The Gaussian defect theorem, tiling to compare δ(m) with δ(√d), and bounded-factor stability of D give the left side of (1). The Poisson and extremal estimates are ordinary proofs, with the single-sided inequality and the finite Gaussian product certified in Lean. An explicit equivalent for R(n) remains open.
