# The primitive signature (13,13,11) and a degree-33 class number

Deldor14 · 28 November 2026 · Research note for mathematical review

Let a,b,c be coprime integers with a¹³+b¹³=c¹¹ and abc≠0. We prove unconditionally that 4·23·1607·1871 divides ab. We also prove that such a solution would force the ordinary class number of the field

    F = ℚ(t),   t³³ + 2t²² − 16t¹¹ + 8 = 0

to be even. In particular an odd class number would exclude all nontrivial solutions. The signature is excluded under GRH using the Selmer rank computed by Best, Dahmen and Freitas in §5.3. The unconditional parity of this degree-33 field is open in this note. Our certified degree-21 calculation for output exponent 7 concerns a different field. [Best–Dahmen–Freitas](https://arxiv.org/html/2510.12092v1#S5.SS3) · [Degree-21 certificate](https://github.com/Deldor14/open-math-agents/tree/1a402d3a79314f68ee53b31e1d9287398cabd18c/research/beal-thirteenth-gap/class-number)

## Descent and its local image

Use K=ℚ(ρ), ρ³+ρ²−4ρ+1=0, s=ρ²−ρ+1, t¹¹=2ρ. The prime 2 is inert in K; the last equation is Eisenstein there. The field F has signature (3,15) and discriminant −2³⁰11³³13²². K has ordinary class number 1 by its discriminant 169 and Minkowski's bound 26/9, since 2 is inert. Let C be the smooth projective curve Y²=X¹¹+c₀ where c₀=4¹⁰s¹¹/ρ², and J its Jacobian. Set θ=−4s/t². Then θ¹¹=−c₀ and K(θ)=F since 11 is prime and t² generates F over K. The known point P has X₀=4s and Y₀=2¹⁰s⁶(ρ²+ρ−5). Write D=[P−∞]. We use odd-degree hyperelliptic 2-descent into the norm kernel in F*/F*². A finite nonbranch point contributes X−θ. [Schaefer's descent](https://www.sciencedirect.com/science/article/pii/S0022314X8571044X)

Let S consist of the primes over 2,11,13. There are three in K. In F their ramification indices and residue degrees are (11,3) over 2, (11,3) over 11, and (3,1),(3,10) over 13. All four are principal by the supplied generators. Outside S the curve has good reduction since its polynomial discriminant is a unit there. Good odd places impose the unramified local condition; this follows from reduction of the étale multiplication-by-two map and equality of the local Kummer and unramified dimensions.

The S-units of F give 22 dimensions modulo squares, those of K give six. Norm splits by inclusion because the relative degree is odd. The S-unit norm kernel V therefore has dimension 16. For each explicit S-unit u the certificate projects to u·N(F/K)(u), using the inclusion K⊂F. Their dyadic localizations have rank **16**. This proves they span V and localization at 2 is injective there. Integrality, norms and prime-ideal equalities are checked directly. The calculations use two descriptions of local square classes. The first uses the group of units modulo the 23rd power of the dyadic prime together with valuation parity. The second removes the residue by raising the unit to the seventh power, then cancels the leading residue successively at the 22 positive depths. The program checks a full residue basis at each depth. The even steps use squares, except for one generator at depth 22. Units at depth 23 are squares by Hensel's lemma, since v(2)=11.

Write d=dim Cl(F)[2]. The norm-kernel classes with even valuations outside S have dimension at most 16+d, by halving these valuations and taking the S-ideal class. The kernel consists of S-units modulo squares. Each quadratic character of the ordinary class group gives a square class unramified at all finite places and split at the real places and at all four principal S-primes. Its norm to K is unramified at all finite places and split at infinity. This holds by local triviality at S and unramified corestriction elsewhere. Since K has class number one the norm is trivial. These d classes lie in the Selmer group, are zero locally at 2 and are independent of V. Thus every class in the larger even-valuation norm kernel decomposes uniquely into an element of V and an ordinary class-group character. In particular any class with trivial dyadic localization is trivial at every explicitly principal prime in F.

At the dyadic place J[2](K₂)=0 because the defining polynomial is irreducible there. The local Kummer dimension is 5·3=15 and fifteen explicit local point classes span it. At 13 the local dimension is one by the two irreducible factors. To obtain its generator, take a primitive eleventh root β in the unramified extension of degree ten of K₁₃. The point abscissa X=4sβ has right side (4s)¹¹(1+1/(4ρ²)) of valuation 12. After division by a uniformizer to the twelfth power the nonzero residue lies in the base residue field and is a square in its even-degree extension. Trace the resulting divisor to K₁₃. Its class is Φ₁₁(θ/(4s)), since the discarded scaling factor is a square. At 11 the relative local extension has odd degree and both square-class dimensions are two, so the norm kernel is zero. At the real places the single real root gives trivial norm kernel as well.

For the joint space of the two tested local images L and the global projected units, the verified dimensions are

    dim V=16,   dim L=15+1=16,   dim(V+L)=29.

All unit classes passing these local conditions meet the good-place conditions. Consequently dim Sel₂(J/K)=3+d. Its dyadic localization has dimension three, with kernel the ordinary class-group characters. The three supported Selmer representatives are products of the projected elements whose one-based indices in elements.json are

    (6,7,13,16),   (4,5,6,7,8,9,12,14,15,16,17),   (4,6,10,13,14,15,16,17,21).

The last agrees locally with D. Under GRH, Best–Dahmen–Freitas report that the total Selmer dimension is three. Thus the dyadic localization is injective under their hypothesis, as it is if Cl(F) has odd order. The elementary and local computations above are unconditional.

## The primitive parameter

Use Best–Dahmen–Freitas, Theorem 1.2 and §§3–4.3. A nontrivial primitive solution has 13∤a+b, and a+b is a nonzero eleventh power. Their sieves at exponent 11 remove the extraneous cyclotomic unit, so a+bζ is an eleventh power in ℚ(ζ), ζ a primitive thirteenth root. Their associated finite point on C has normalized coordinates x=X/X₀, y=Y/Y₀. Write w=ab/(a+b)². Their quartic and quadratic identities give

    x¹¹=1+(ρ−4)w+s w²,       y=1−2(ρ²+1)w/5.

At the dyadic place it is useful to put v=(y−1)/2 and A=ρ²/(1+4ρ²). The curve becomes v²+v=A(x¹¹−1). This gives good reduction with a single point at infinity. On the affine chart the derivative in v is a unit in the special fiber. At infinity, T=x⁵/v and U=1/x give U+T U⁶=A T²(1−U¹¹), a smooth chart at U=T=0. [Best–Dahmen–Freitas, §§3–4](https://arxiv.org/html/2510.12092v1#S3)

## Unconditional exclusions

For q=23,1607,1871, first suppose q∤a+b and set u=a/(a+b) modulo q. Then u+(1−u)ζ must be an eleventh power. In the product algebra over 𝔽q defined by Φ₁₃, each residue field has degree j=ord₁₃(q), and all components of this expression are nonzero. Raising to (qʲ−1)/11 in all components leaves only u=0,1. If q divides a+b, then a(1−ζ) must be an eleventh power. The same exponent gives a nonscalar value on 1−ζ, which no scalar a can correct. The verifier enumerates every u by exact polynomial arithmetic. Hence all three q divide ab and none divides a+b.

If a+b is even, v₂(a+b)=11k for k≥1. Then v₂(w)=−22k, v₂(x)=−4k and v₂(X)=2−4k. The unit 1+c₀/X¹¹ is a square, so the curve equation makes X a square locally. In the dyadic completion of F the element θ/X has valuation at least 42, hence X−θ is a square as well. The global Kummer class must consequently be an ordinary class-group character. At every principal prime of F it must be locally trivial.

At q=1607 and ρ≡793 there are eleven degree-one primes of F. Explicit elements generate them all. Since u=0 or 1, w=0 modulo q and x¹¹=1. For each of these eleven possible abscissas x the projected Kummer values of X−θ at the eleven primes include six nonsquares. The residue test for X≡θ uses the derivative 11θ¹⁰, by the curve equation. Thus the dyadically trivial class cannot arise. The same independent obstruction occurs at 1871 with ρ≡742. This eliminates a+b even.

If v₂(ab)=1, then w≡2 modulo 4, and x≡1+2ρ modulo 4. Indeed the unit-group reduction in 𝔽₈ has order 7, coprime to 11. In F the ratio of 1+t²x to 1+t²(1+2ρ) differs from 1 at depth at least 24. The dyadic class of X−θ is consequently that of 4s(1+2ρ)−θ. Adjoining this candidate to the entire dyadic S-unit norm kernel increases the rank from 16 to 17. All ordinary class-group characters vanish there, giving a contradiction. This proves 4·23·1607·1871 divides ab unconditionally.

## A conditional exclusion of the remaining branch

We explain why injectivity of dyadic Selmer localization excludes the case 4|ab. Let O be the ring of integers of K₂, an unramified cubic extension of ℚ₂, and use the regular differentials ηᵢ=xⁱ dx/(1+2v), 0≤i≤4. The invariant logarithm of the formal reduction kernel J₁ takes values in (2O)⁵, and induces an isomorphism J₁→(2O)⁵. Here are details. Choose points above four distinct finite abscissas of the special fiber, with abscissa residues 1,1+ρ,1+ρ²,1+ρ+ρ², and add infinity. The degree-five divisor with one point in each of these five disks is nonspecial. The evaluation matrix of the differentials is invertible by the Vandermonde determinant on the four finite abscissas and the last coordinate at infinity. Thus the Abel map from this product of disks gives coordinates on J₁ by Hensel's lemma. Integrating integral power series for the differentials at arguments in 2O gives values in 2O. On the depth-two kernel J₂ the logarithm is an isomorphism onto (4O)⁵ by the formal group logarithm at depth two. Reduction gives |J₁/J₂|=2¹⁵. The logarithm is injective on J₁ because its kernel is 2-primary torsion and J(K₂)[2]=0. These facts give the claimed equality of lattices.

The reduction Jacobian has odd order. Indeed the Artin–Schreier double cover is unramified over the affine line and has one ramified point at infinity. Modulo 2, either splitting type at a finite closed point of degree j contributes the factor (1−T²ʲ)⁻¹ to the curve zeta function. Their product is the zeta function of the affine line at T², congruent to 1 modulo 2. Including infinity shows that the Weil numerator is 1 modulo 2. Its value at 1 gives odd order. Thus J₁/2J₁→J(K₂)/2J(K₂) is an isomorphism. Equivalently the normalized logarithm log/2 modulo 2 identifies the latter group with 𝔽₈⁵. Write the residue of ρ as r, with r³+r²+1=0.

To identify the dyadic Selmer image in these coordinates, shift a finite local point horizontally by 2h, staying in the same disk, for h=1,ρ,ρ². If the initial abscissa reduces to b, its log/2 has coordinates

    bⁱ h + (i mod 2) bⁱ⁻¹ h²  in 𝔽₈,     0≤i≤4,

with zero second term when i is even. Integration over a displacement 2h leaves only the constant and linear terms after division by 2 and reduction. The derivative of the denominator contributes a factor 2 and vanishes. The Kummer class of this difference is given by (1+t²(x+2h))/(1+t²x). At infinity shift T from 0 to 2h. The local differential is −U⁴⁻ⁱ dT/(1+6T U⁵+11 A T² U¹⁰), by differentiating the chart above. Its normalized integral reduces to (0,0,0,0,h). Here U=A T²(1+O(T¹¹)); replacing U by A T² changes the Kummer class by a local square. Thus the Kummer representatives for the three infinity shifts can be computed as s/(A h²)−θ. Both descriptions use the same fixed differential basis.

These fifteen tiny-integral vectors are a basis. The GP verifier computes their Kummer images and expresses the three Selmer images in this basis. The binary coefficient masks in the stated order are 8336, 29771 and 9056. Two independent local square-class calculations give the same coordinates. Packing the three coefficients of each residue field element in ascending powers of r and then packing the five field elements in ascending differential degree, the eight normalized-log residues are

    0, 4273, 10873, 15048, 16697, 20872, 27456, 31729.

For a hypothetical solution in the remaining branch, k=v₂(w)=v₂(ab)≥2, and its point Q lies in the disk of P. In fact x−1 has valuation k and (x−1)/2ᵏ reduces to r, by the normalized eleventh-power equation and w/2ᵏ≡1. The integral from P to Q has the same first digit in all five coordinates. Higher terms have strictly greater valuation because k≥2 and the power series have integral coefficients. Thus

    log([Q−P])/2ᵏ mod 2 = (r,r,r,r,r),   packed value 9362.

This lies outside the eight-element Selmer image. Suppose now that dyadic Selmer localization is injective. A global Jacobian point divisible by 2 locally is divisible by 2 globally, by injectivity on its Kummer class. Repeating k−1 times gives a global point B with 2ᵏ⁻¹B=[Q−P], since the local group has the stated logarithm lattice, odd-order reduction and no rational 2-torsion. Then log(B)/2 modulo 2 is the excluded vector. This contradiction completes the conditional proof. This is an explicit instance of Selmer-group Chabauty along the rational one-parameter locus w. [Stoll, Chabauty without the Mordell–Weil group](https://arxiv.org/abs/1506.04286)

## Reproduction and scope

Run in this directory with PARI/GP 2.19.1 and Python 3.8 or later.

    gp -qf -s 256M verify.gp
    python3 finite.py

The committed integer arrays contain all S-unit candidates and principal-ideal generators used by the certificate. Neither verifier assumes a class number. LocalIdentities.lean was checked with Lean 4.33.1 and Mathlib. It covers the quartic identity, the differential identity at infinity, and the last finite exclusion. The unconditional rank formula, divisibility obstruction and conditional conclusion use the written arguments above. A preliminary PARI class-group calculation suggests h(F)=1. The missing unconditional step is a proof of odd class number, or another proof that dyadic localization is injective on the Mordell–Weil classes needed for halving. The conditional exclusion has not undergone external mathematical review.
