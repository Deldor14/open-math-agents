# A large progression-free set with bounded Gaussian midpoint leakage

Write R(n)=r₃(n) for the maximum size of a 3-progression-free subset of [0,n) in the integers and D(t)=log(⌈t⌉/R(⌈t⌉)). Fix κ>0. There exists a progression-free B⊂[0,n) such that, as n tends to infinity,

    |B| ≥ R(n) exp{−D(√log n)−Oκ(1+√log log log n)},
    Wκ(B) := Σ_(x,y,z∈B) exp{−κ(x+z−2y)²} ≤ Cκ |B|.                  (1)

All triples are ordered, with repetitions allowed. The diagonal alone contributes |B|. The bound controls the total weighted contribution of all nonzero integer defects. In particular the number of ordered triples with |x+z−2y|≤h is at most Cκ exp(κh²)|B| for any fixed h. The set B can depend on κ. The proof uses only interval partition, carry-free products and [Behrend's bound](https://doi.org/10.1073/pnas.32.12.331).

## Separating high and low digits

Choose H=⌈K√log n⌉ with K depending only on κ, h=⌊H/10⌋, m=⌊n/H⌋. Above a fixed cutoff h≥1, m≥1 and h<n/2. Take a maximum free A⊂[0,m) and a nonempty free E⊂[0,h). Then B=HA+E is a direct product inside [0,n). For three of its points the defect is HΔ_A+Δ_E, where |Δ_E|≤2(h−1). When Δ_A=0 all three high digits coincide since A is free. These triples contribute exactly |A|Wκ(E). All remaining triples have |HΔ_A+Δ_E|≥4H/5. Their total weight divided by |B| is at most n² exp(−16κH²/25), which is ≤n⁻⁴ for K²≥150/(16κ). In particular B is 3-progression-free and

    Wκ(B)/|B| ≤ Wκ(E)/|E| + n⁻⁴.

Choose E recursively by the same prescription at length h, stopping with a singleton below the fixed cutoff. Along every chain the lengths strictly decrease, so the sum of errors is bounded by Σ n⁻⁴. This proves the second estimate of (1).

## Cardinality

Partition [0,n) into at most 2H intervals of length ≤m for n sufficiently large. Each contains at most R(m) points of an optimal set. If L(n)=log(R(n)/|B|), this yields

    L(n) ≤ D(h) + L(h) + log(2H/h).

The final term is bounded. Changing an interval length by a bounded positive factor changes D by at most a constant depending on that factor, by partitioning the larger interval and by monotonicity of R. Thus D(h)=D(√log n)+Oκ(1). At every later length t one can use D(t)≤C(1+√log t) by Behrend. The second recursively chosen length is Oκ(√log log n). Above a sufficiently large fixed cutoff, the logarithm of each successive length is at most one quarter of the preceding logarithm. Summing the square roots of these logarithms, and the additive constants, costs Oκ(1+√log log log n). Bounded lengths are absorbed by the stopping convention. This proves (1).

In [the degree-only selection problem](DegreeOnly.md), Gaussian leakage bounds the expected number of candidate progressions despite the intrinsic noise of a degree measurement. The assertion here concerns the true integer extremal number and does not require a random model.

[WeightedDefect.lean](WeightedDefect.lean) verifies the four finite steps for general integer digit sets: cardinality, freeness, the weighted product estimate and its normalized version. The iteration and its logarithmic loss are written proofs.
