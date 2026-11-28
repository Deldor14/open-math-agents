# Four local steps suffice on the sampled integer interval

In the independent sample of [1,N] with retention probability p, put d=Np², suppose d→∞ and log d=o(log N). Reveal only the unordered three-term-progression hypergraph, with independent uniform random marks. Distances count steps across a hyperedge. A radius-three rule can propose candidates for which a single additional step deleting every candidate in an all-candidate edge leaves, in expectation and with probability tending to one, at least

    c Np r₃(⌈d⌉)/⌈d⌉

points. The effective-length upper bound gives the same order for the unrestricted optimum. On the continuum tree, the supremum V₄(d) of this root survival probability over all measurable radius-three candidate rules consequently satisfies V₄(d) ≍ r₃(⌈d⌉)/⌈d⌉. The optimizing rule may depend on d. [Interval experiment and nine-step proof](IntervalLocalRecovery.md) · [Effective-length estimate](https://github.com/Deldor14/open-math-agents/blob/68cd54337b3e1a61aeca710263c2e0f012292c8c/research/erdos142-hinge/RothEffectiveLength.md)

## Eighth moments for the folded coordinate

Use the same split Poisson tree, preliminary measurement s, intervals Iⱼ, conditional bias bounds and estimators Zⱼ as in the nine-step proof. Put t=|x/N−1/2|. At each of j=1,2,3, uniformly over types t∈Iⱼ and good preliminary measurements s (|s−t|≤σ), we have

    E[|Zⱼ−t|⁸ | x,s] ≤ Cⱼ(d^(−4j)+N⁻⁸+exp(−cⱼd)).                         (1)

For the first level, conditional on s the independent second-class count has Poisson mean λ=d(1−t)/2+O(d/N). Its eighth central moment is λ+119λ²+490λ³+105λ⁴ by differentiating exp(λ(exp u−1−u)). Division by (d/2)⁸ gives O(d⁻⁴), the bias before clipping is O(1/N), and projection onto [−1,1] only decreases the distance to t.

At a later level, condition on the second-class edge types, the split and the preliminary measurements of their children, exactly as in the earlier proof. Outside an event of conditional probability O(exp(−cd)), there are m≥c'd kept edges, all straddling the true folded midpoint with both child types in Iⱼ₋₁. The estimate is the average of m conditionally independent endpoint averages. The expectation of each differs from t by O(N⁻¹+exp(−cd)) uniformly, by the existing bias bound. Each centered endpoint average has conditional eighth moment at most C times the preceding bound, by convexity and centering. Selection only uses preliminary classes, leaving the second-class subtrees used in those estimates independent.

If m independent centered real variables have eighth moments at most M, their normalized sum has eighth moment ≤C M/m⁴. To see this, expand the eighth power. Any term with a singleton index has zero expectation. The remaining index tuples use at most four distinct indices, thus number O(m⁴). The expected absolute value of each product is ≤M by Hölder, using the multiplicities as exponents. Adding back the conditional bias, and using boundedness on the exceptional event, proves (1).

## Screening and deletion

Keep q=⌈100d⌉, an optimal alphabet in [0,⌊q/20⌋), and the gate, acceptance intervals and final deletion from the nine-step proof. Substitute Z₃ for Z₈. On a good preliminary measurement passing the gate, the true folded type is in I₃. At j=3, Markov at error threshold 1/(36q) gives an ideal bad-root probability O(d⁻⁴). Coupling to the finite interval costs O(N^(−1/20))=o(d⁻⁴). The sampled degree has conditional second moment O(d²). Cauchy–Schwarz bounds the expected total number of bad root-edge incidences by O(Np/d). Bad isolated roots cost at most O(Np/d⁴) in the lower bound on candidate count.

Every other candidate is in its true outer alphabet cell. Every triple of good candidates is contained in one cell, by the previously verified folded-position and rounding lemmas. The same elementary edge count therefore gives

    E[output]/(Np) ≥ (R(⌊q/20⌋)/q)(1/12−3d/(8q))−O(d⁻¹).

Tiling and Behrend absorb the error. The two-root coupling and fixed-d continuum limit in the earlier proof apply at depth four, giving concentration and the comparison for V₄. The full probability argument is a written proof. The existence theorem does not assert that four is the minimum possible radius.

[AveragedEighthMoment.lean](AveragedEighthMoment.lean) certifies the cancellation of singleton terms, the count of the remaining index tuples and the eighth-moment bound with constant 8·4⁸ for arbitrary independent finite laws. For bounded general laws one may also round each variable to a finite grid, recenter and pass to the limit by dominated convergence.
