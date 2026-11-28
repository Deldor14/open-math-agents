# Which rates can be distinguished by scalar inequalities for the Roth number?

Let R(n) denote the maximum cardinality of a subset of [0,n) without a nonconstant three-term arithmetic progression. For every 0<γ<1, every ℓ>0 and any prescribed finite prefix of R there is a nondecreasing integer sequence H, with H(0)=0 and increments in {0,1}, satisfying

    H(n) ∼ c n exp(−ℓ(log n)^γ)     for some c>0,
    H(a+b) ≤ H(a)+H(b),
    H(a)+H(b) ≤ H(a+2b−1)                               (1≤a≤b),
    H(m)H(n) ≤ H(mn+(m−1)(n−1))                         (m,n≥1).

It agrees with R throughout the prefix. Every fixed signed inequality of the form

    Σ cᵢ R(⌊aᵢn⌋+eᵢ) ≥ 0                               (1)

that holds eventually for R and has a nonzero exponential polynomial P(z)=Σ cᵢ aᵢᶻ also holds eventually for this same H. Here aᵢ>0, cᵢ are real, and eᵢ are fixed integers. In addition one can prescribe finitely many such rules with P(1)>0 that hold for R at every positive input with all arguments nonnegative. H then satisfies these prescribed rules at every positive input as well. The eventual threshold for the other rules can depend on the rule.

Thus throughout the interval 1/6<γ<1/2 the same structural conditions, any finite initial data and all the fixed signed multi-length tests are consistent with mutually different growth rates inside the classical density bounds. The construction also works for γ outside this interval if the density bounds are omitted. The centered product has H on both inputs and at the output. No global comparison between H and R is assumed.

## The prefix and a power mixture

Choose ε>0 sufficiently small for the finite list, with ε<1/100. The good dyadic centers in [MixedGoldenRules.md](MixedGoldenRules.md) give a positive integer P₀, as large as desired, and a sequence B(n)=max(R(n),⌈n/P₀⌉) that agrees with R through an arbitrarily long prefix. It is subadditive, has unit-bounded increments and satisfies the one-site join. Beyond some S₀ it is exactly the ceiling. The same choice handles both signs in the finite list. Indeed, whenever a ceiling strictly wins at any argument, all the arguments are within fixed factors of that argument for large n. In this range the cited dyadic-center argument gives

    m/P₀ ≤ B(m) ≤ (1+O(ε))m/P₀+1.

Use the lower bound for positive cᵢ and the upper bound for negative cᵢ. The strict slope P(1)>0 pays all multiplicative errors and all bounded argument and rounding errors since n/P₀ is large at the first possible crossover. If no ceiling wins at any argument, apply (1) to R. One can also ensure T/P₀ is as large as desired, where T is the prefix through which B=R. [Prefix proof and one-site join](FinitePrefix.md)

For a probability law ν on [θ₀,1), with θ₀>log(2)/log(3), put J(u)=∫u^θ dν(θ) for u>0. We will choose a small atom and keep the rest of the law arbitrarily close to 1. Choose X≫S₀P₀ large enough that R(m)≤m/(2P₀) for m≥X, and that X/P₀ absorbs the finitely many constants below. Then choose ν so that

    J(u)≥(1−ε)u  on 1≤u≤KX,

where the fixed K≥2 exceeds twice the largest ratio of input dilations in a prescribed rule. This can be achieved by making the atom sufficiently small and bringing the remainder of the support arbitrarily close to 1. Also, for each of the finitely many prescribed rules,

    ∫ P(θ)u^θ dν(θ) ≥ c₀ u^θ₀    (u≥1).                                  (2)

For concreteness, place the atom at θ₀. For θ sufficiently close to 1 every prescribed P(θ)≥P(1)/2. The atom contributes at worst minus its mass times |P(θ₀)|u^θ₀. The positive lower constant c₀ can be fixed in terms of the slopes P(1) before choosing X. For x,y≥1 positive covariance gives J(xy)≥J(x)J(y): integrate (x^θ−x^ψ)(y^θ−y^ψ)≥0 over two independent exponents.

Set G(t)=(X/P₀)J(t/X) for t>0, G(0)=0. Use f(t)=t/P₀ up to X and f=G after X. The function f is increasing and concave, including at X since the right derivative is at most 1/P₀. Its Lipschitz constant is at most 1/P₀. Let H(n)=B(n) for n≤X and H(n)=⌈G(n)⌉ otherwise. The formulas agree with ⌈f⌉ near X. This proves the assertion on increments. If a+b≤X, splitting holds for B. For a+b>X use subadditivity of f and H≥⌈f⌉ at each input.

## The join and the product at every length

For z=a+2b and 1≤a≤b the extension G to all positive arguments satisfies

    G(z)−G(a)−G(b) ≥ (3^θ₀−2)G(b).

Indeed (2+v)^θ−v^θ−1 decreases in v=a/b≤1 for 0<θ<1. For a,b≤X we have G(t)≥t/P₀. For any input t, H(t)≤G(t)+S₀+1, since the ceiling agrees with B for S₀<t≤X. If z−1≤X use the join for B. Otherwise b≥X/3, so G(b)≥X/(3P₀), and the surplus absorbs both bounded input errors and the loss from z to z−1 (at most one on [X,∞)). This proves the join.

Write S=mn+(m−1)(n−1) with 2≤m≤n; m=1 is equality. Then 5mn/4≤S≤2mn.

* For n≤X, if H=R at both inputs, use the genuine centered product for R. For S≤X the result follows from B≥R. When X<S≤2X², near-linearity gives H(S)≥(1−ε)S/P₀≥R(S). If a ceiling wins, at that input t it is at most (1+ε)t/P₀ by the choice T/P₀≫1/ε. At the other input H(u)≤u. Hence H(m)H(n)≤(1+ε)mn/P₀, and H(S)≥(1−ε)S/P₀ dominates this whether or not S crosses X.
* For m≤X≤n, G(S)/G(n)≥J(S/n)≥(1−ε)S/n by covariance and S/n≤2X. Also H(n)≤(1+ε)G(n), H(m)≤m. The factor 5/4 absorbs the two errors.
* For X≤m≤n, covariance twice gives G(mn)≥(P₀/X)J(X)G(m)G(n)≥(1−ε)P₀ G(m)G(n). Both ceilings cost at most a factor 1+ε and P₀ can be taken greater than four.

The true centered product used at the beginning follows by placing translated AP-free blocks at spacing 2m−1, with the final block requiring only m sites. Its total extent is (2m−1)(n−1)+m=S. [Earlier centered-product proof](ProfileDilation.md)

## Signed tests at every prescribed input

If all arguments are ≤X, the prefix construction applies. If some argument exceeds X but n<X (or some other argument is ≤X), all arguments lie between fixed multiples of X. For X sufficiently large they all exceed S₀. Each H-value differs from its linear prediction m/P₀ by at most εm/P₀+1 using the near-linearity of J on bounded ratios. The strict slope pays the total error as above. In the remaining case n≥X and all arguments exceed X. Extend G across X in evaluating the unshifted lengths if necessary. Its derivative is bounded on [X/2,∞) by 2/P₀, since all exponents lie in (0,1). Fixed offsets and ceilings therefore affect the sum by O(1). Its unrounded value is (X/P₀)∫P(θ)(n/X)^θ dν, which dominates this error by (2).

For any other eventually valid (1), [the signed variation theorem](SignedScaleVariation.md) implies P(θ)>0 throughout some punctured left neighborhood of 1. The law constructed below gives positive mass in every such neighborhood. A fixed band of positive mass where P>0 and θ strictly exceeds every θ with P≤0 supplies a positive power dominating both negative contributions and bounded rounding errors. This proves the simultaneous eventual assertion for all fixed nondegenerate signed rules; it requires no uniformity over the family.

## Prescribing the deficit exponent and its coefficient

Put p=γ/(1−γ). On 0<s<s₁ give s=1−θ density proportional to

    s^(−(p+2)/2) exp(−a s^(−p)),

with s₁ as small as needed above. Choose a>0 so that (p+1)a^(1/(p+1))p^(−p/(p+1))=ℓ. Supply the remaining positive atom as above. For u=eᵗ the continuous part of J(u)/u is the Laplace integral with exponent −ts−a/sᵖ. Its minimizer is s*=(ap/t)^(1/(p+1)). On substituting s=s*v the large parameter is λ=a/(s*)ᵖ and the phase is v^(−p)+pv. It has a unique nondegenerate minimum p+1 at v=1. The prefactor (s*)^(−p/2) cancels the Gaussian factor λ^(−1/2). The contribution outside any fixed neighborhood of 1 is exponentially smaller than the main term: for λ≥1 one can bound the tail by exp(−(λ−1) inf phase) times the integrable v^(−(p+2)/2)exp(−phase). Thus J(u)∼c₁ u exp(−ℓ(log u)^γ), with c₁>0. The atom decays relative to this term. The constant shift log(n/X)=log n−log X changes its exponent by o(1). Rounding preserves the claimed equivalent for H.

## Simultaneously positive differences of orders up to a linear threshold

One can arrange one more property of this same integer H. Define uₖ=H(2ᵏ)/2ᵏ, and let Δvₖ=vₖ−vₖ₊₁. Let α*=0.2334861261… solve

    (1+α)^(1+α) (3/2)^α = 2 α^α.

Then Δʰuₖ>0 for every sufficiently large k and every integer 0≤h≤α*k, including equality in the bound. This provides a countermodel to deductions of a negative difference in this smaller range solely from the structural rules of the theorem. The [negative-differences theorem for R](NegativeDyadicDifferences.md) uses a larger range of orders.

To see this, the log of the right side divided by the left decreases strictly from log 2 to a negative value at 1/4, so there is a unique positive root below 1/4. Put y=1/(1+α*) and θ₀=1+log₂ y. Then θ₀>log₂(8/5)>log(2)/log(3) (the last comparison also follows from 8/5>2^(2/3) and 3^(2/3)>2). Choose a fixed positive atom mass w small enough for the finite-list tests and near-linearity, and then increase X so wX^(1−θ₀)/P₀≥1/2. The rest of ν can be placed as close to 1 as needed after that choice.

For all k with 2ᵏ>X the unrounded dyadic density is a mixture of functions vᵏ with v=2^(θ−1)∈(0,1), with positive weights X^(1−θ)/P₀ dν(θ). Its h-th difference is nonnegative termwise and the chosen atom contributes at least (1/2)yᵏ(1−y)ʰ. The ceiling adds an error eₖ between 0 and 2⁻ᵏ. Only the odd binomial terms in Δʰeₖ can be negative. Their total absolute contribution is at most

    2^(−k−1) [(3/2)^h−(1/2)^h].

At h≤α*k the defining equation gives (2y)ᵏ[(1−y)/(3/2)]ʰ≥1. The positive atom therefore strictly exceeds the one-sided error. In the single-atom argument y(1−y)^α is maximized at y=1/(1+α), which explains the choice. No optimality among other integer models is needed.

[MixtureRounding.lean](MixtureRounding.lean) checks the one-sided error, atom estimate, maximizing location and endpoint criterion. [HybridCenteredProduct.lean](HybridCenteredProduct.lean) checks the product across the integer splice with all actual ceilings. The construction of ν, the signed-rule argument and the asymptotic equivalent are written proofs.
