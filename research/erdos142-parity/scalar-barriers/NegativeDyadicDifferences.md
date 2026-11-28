# Negative differences of the true dyadic Roth densities

Let aₖ=R(2ᵏ), uₖ=aₖ/2ᵏ, and D uₖ=uₖ−uₖ₊₁. Put α₀=2/log₂(3/2), approximately 3.41902. For each fixed α>α₀ there is a constant C such that for every sufficiently large integer T,

    Dʰ uₖ < 0   for some T≤k≤C T⁴ log T and 1≤h≤αk.                        (1)

This is a statement about the genuine interval Roth number. In contrast, [the signed moment estimate](SignedScaleVariation.md) proves quantitative positivity at infinitely many indices for **each fixed** h. The negative result allows h to grow with k. It excludes eventual complete monotonicity and even positivity in the indicated linear range of orders. A sequence of integer counts with the same two classical density envelopes can keep all its differences strictly positive up to order k/8 at every sufficiently large k.

## An integer functional and a Bernstein polynomial

Define the linear functional ℓ on real polynomials by ℓ(xʲ)=aⱼ. It takes integers on polynomials with integer coefficients. For y=x/2 one has

    ℓ(xᴷ yⁱ(1−y)ʰ) = 2ᴷ Dʰu_(K+i).

The identity follows by expanding (1−y)ʰ. Thus positivity of the differences makes ℓ nonnegative on the corresponding Bernstein basis polynomials times xᴷ. No measure representation is assumed.

Fix α>α₀. Choose an integer s≥1, let d=6s, and take

    q(x)=[x(x−2)(x−1)²]ˢ,       A=⌈d/α⌉,       P(x)=xᴬq(x).

In degree d the Bernstein coefficients of q on [0,2] have absolute value at most η=(d+1)(8/27)ˢ. To see this homogenize on y+z=1, x=2y. The polynomial giving the signed coefficients before dividing out their binomial weights is

    (−4yz)ˢ (y−z)²ˢ (y+z)²ˢ = (−4yz)ˢ(y²−z²)²ˢ.

Taking absolute values coefficient by coefficient yields [4yz(y²+z²)²]ˢ. For y,z≥0, y+z=1, its maximum is (8/27)ˢ because max 4v(1−2v)²=8/27 for 0≤v=yz≤1/4. At y=i/d the binomial weight of index i is maximal among the d+1 weights and hence at least 1/(d+1), including the endpoints. This gives the asserted bound on each normalized coefficient. Since log₂(27/8)=3 log₂(3/2), take s sufficiently large that 2ᴬη<1. All of A,d,q,P now depend only on α.

For a smaller certificate at α=9 one can take p=x(x−1)(x−2), q=p⁵, d=35 and A=4. The seven-degree Bernstein coefficients of p have absolute value ≤4/7; raising to the fifth power gives η=(4/7)⁵ and 16η<1. The [Lean certificate](BernsteinInteger.lean) verifies the degree-seven polynomial identity and coefficient bound, the difference identity and the ordered-word expansion for any power of p. The sharper constant above and the localization below are written arguments.

## A cone of nonnegative differences forces an integer recurrence on a long block

Let b=deg P. Suppose Dʰuₖ≥0 whenever T≤k≤J and 0≤h≤αk. Choose an integer M=⌈T/A⌉+O(1) so large that 2ᵇ(2ᴬη)ᴹ<1. For

    M≤m≤m₁=⌊(J−b)/(A+d)⌋,                 0≤j<b,

one has ℓ(xʲPᵐ)=0. Indeed put K=Am+j and expand qᵐ as products of m individual Bernstein polynomials. The coefficient product at any word has absolute value at most ηᵐ. The unsigned basis product is a positive constant times yⁱ(1−y)^(dm−i). Its ℓ-value after multiplication by xᴷ is nonnegative by assumption: its index K+i lies in [T,J], and its order dm−i≤dm≤αAm≤α(K+i). Summing the unsigned basis products gives 1 by the binomial theorem, so

    |ℓ(xʲPᵐ)| ≤ ηᵐ a_(Am+j) ≤ 2ʲ (2ᴬη)ᵐ < 1.

The value is an integer and must vanish. Since P is monic, the polynomials xʲPⁿ, 0≤j<b, 0≤n≤m₁−M, form a triangular basis through degree b(m₁−M+1)−1. It follows that

    ℓ(Pᴹ xⁱ)=0    for 0≤i<b(m₁−M+1).

Writing S for the forward shift on the integer sequence a, this means that P(S)ᴹa vanishes over these consecutive starting indices. Extend the initial bM terms by the monic recurrence P(S)ᴹ=0. The extension agrees with the true a at least through index b(m₁+1)−1. If the entire infinite cone had nonnegative differences from any T on, it would give an eventual recurrence with characteristic roots only 0,1,2. After division by 2ᵏ its polynomial contribution from the root 2 would have to tend to zero by Roth; the remaining sequence would grow at most polynomially, contradicting Behrend. We next quantify how far agreement can persist.

## Length of the block

The recurrence polynomial is x^(K₀)(x−1)ʳ(x−2)ᵛ, where K₀,r,v are fixed positive integer multiples of M. After discarding K₀ initial terms, the generating function of the extended sequence is

    N(z) / [(1−z)ʳ(1−2z)ᵛ],        deg N < r+v.

The coefficients of N are at most exp(C₁M) in absolute value. Indeed its numerator is determined by the first r+v remaining terms, all true values ≤2^(K₀+r+v); multiplying by the denominator costs at most 2ʳ3ᵛ in coefficient norm. The principal part at z=1 has the form Σⱼ₌₁ʳ cⱼ(1−z)⁻ʲ with each |cⱼ|≤exp(C₂M). This follows by expanding N(z)/(1−2z)ᵛ about 1 on the circle |z−1|=1/4, where |1−2z|≥1/2, and using the coefficient bound on the first r Taylor terms. All constants in this paragraph may depend on α but do not depend on the data, T or J.

The coefficient of index l from this principal part is at most exp(C₂M) r binom(l+r,r). The other principal part, at z=1/2, contributes 2ˡ times a polynomial in l of degree <v. Consequently for some polynomial W of degree <v, and all k≥C₃ M in the range of agreement,

    aₖ/2ᵏ = W(k) + O(exp(−c₃ k)).                                         (2)

For this estimate set l=k−K₀ and bound binom(l+r,r) by [e(1+l/r)]ʳ. Its logarithm and the C₂M term are less than k log(2)/2 for all k≥C₃M on choosing C₃ sufficiently large. The change from l to k and the division by 2^(K₀) are absorbed in W.

Now take t₀=⌈C₃M⌉, X=⌈K M³ log(2+M)⌉ and Z=MX, with a fixed large K to be chosen. Choose J a fixed multiple of Z so that the true sequence agrees with the recurrence through Z. At every integer x∈[X,Z], (2) and Raghavan's Theorem 1.4 give

    |W(x)| ≤ C₄ exp(−c₄ (X/log X)^(1/6)).

The same bound, with a factor of two, holds on the entire real interval. For details, map [X,Z] to [−1,1] and expand the polynomial in Chebyshev polynomials. By cosine orthogonality each coefficient has magnitude at most twice the supremum on the interval. The derivative of the j-th Chebyshev polynomial is bounded there by j², from |sin(jθ)|≤j|sin θ|. Thus in the original variable |W'|≤C(v+1)³ sup|W|/(Z−X). The distance from a maximizing real point to an integer is at most one, and (v+1)³/(Z−X) tends to zero.

At t₀ the transformed argument has magnitude at most 1+2X/(Z−X). The Chebyshev formula Tⱼ(cosh z)=cosh(jz) gives

    |W(t₀)| ≤ C₅(v+1) exp(C₅v√(X/(Z−X))) sup_[X,Z] |W|.

Here v√(X/(Z−X))=O(√M), with the constant independent of K. For fixed K and sufficiently large M, log X≤4 log M, so (X/log X)^(1/6)≥(K/4)^(1/6)√M. Take K large enough that the upper bound for |W(t₀)| and the error in (2) contradict Behrend's lower bound a_(t₀)/2^(t₀)≥exp(−C₆√M). This proves (1). The two estimates on R used here are the same as in [the positive signed-variation theorem](SignedScaleVariation.md).

## Why a sublinear bound on h requires further information about R

Let vₖ=∫₀¹ yᵏexp(−1/(1−y))dy, let a*ₖ=⌈2ᵏvₖ⌉ and u*ₖ=a*ₖ/2ᵏ. The unrounded density is exp(−Θ(√k)): use yᵏ≤exp(−k(1−y)) for the upper bound and integrate over 1−y between 1/√k and 2/√k for the lower bound. Rounding adds at most 2⁻ᵏ. The difference Dʰvₖ is the same integral with the extra factor (1−y)ʰ, and is at least c(2/3)ᵏ(1/4)ʰ by restricting to y∈[2/3,3/4]. The total error from rounding in Dʰ is at most 2⁻ᵏ(3/2)ʰ. Since (4/3)⁸>6, all h≤k/8 have Dʰu*ₖ>0 for large k. These integer data satisfy the two asymptotic density envelopes. They demonstrate why (1) uses orders growing with k and leave the true least negative order open.
