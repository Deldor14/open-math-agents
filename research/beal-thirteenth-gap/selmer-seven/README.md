# A class-group formula for the descent in signature (13,13,7)

Deldor14 · 28 November 2026 · Research note for mathematical review

Let K=ℚ(ρ), where ρ³+ρ²−4ρ+1=0, put s=ρ²−ρ+1, and let J be the Jacobian over K of the genus-three curve

    C : Y² = X⁷ + 4⁶s⁷/ρ².

This is the curve C₇ of Best, Dahmen and Freitas, §5.2, used for the primitive equation a¹³+b¹³=c⁷. Define F=ℚ(t) by t²¹+2t¹⁴−16t⁷+8=0, choosing ρ=t⁷/2. We obtain the following equality of dimensions over the field with two elements, with the ordinary ideal class group on the right.

    dim Sel₂(J/K) = 1 + dim Cl(F)[2].

The certificate proves the unit contribution and computes the relevant local subspaces without a class-group assumption. Thus proving the ordinary class number of this particular degree-21 field odd would give the rank-one Selmer input used in §5.2. A preliminary PARI computation predicts class number 1 under GRH. Its parity remains unproved here. The general signature (13,13,7) has not been settled unconditionally by this note. [Best–Dahmen–Freitas](https://arxiv.org/html/2510.12092v1)

## The field and its units

The identity t⁷=2ρ gives a zero θ=−4s/t² of X⁷+4⁶s⁷/ρ². Conversely, if z=θ/(4s), then t=−2ρz³. The cubic polynomial for ρ is irreducible, totally real, and has discriminant 169. Its reduction is irreducible at 2 and 7, and its translate by 4 is Eisenstein at 13. Thus K has discriminant 169 (an index 13 would give a number field of discriminant 1). Its Minkowski bound is 26/9, and 2 is inert, so its ordinary class number is 1.

Over K the seventh-root equation is Eisenstein at 2, giving degree seven. At 7 the shift by (2ρ)⁴⁹ is Eisenstein: (2ρ)³⁴³−2ρ has coefficients (28,14,21) modulo 49 in the cubic power basis. At 13 its reduction is x⁷−8, with separable factor degrees 1,2,2,2. Consequently F has one prime each over 2 and 7 and four over 13. It has signature (3,9). The local Eisenstein bases at 2 and 7, the relative polynomial discriminant and the tower discriminant formula give disc(F)=−2¹⁸7²¹13¹⁴. Let S comprise these six primes of F, or the corresponding three primes of K according to the field under discussion.

The first twelve rows of elements.json specify −1 and eleven ordinary units. Each row gives a common denominator, coefficients in increasing powers of t, and the signed rational norm. Integrality follows term by term from t⁷=2ρ. The verifier takes the exact determinant of multiplication and obtains norm ±1. Evaluating the units at twelve degree-one primes above 5,31,47,53 gives a rank-12 matrix of quadratic characters. These evaluation maps are legitimate since the polynomial discriminant is supported on 2,7,13. By Dirichlet's theorem the full dimension of ordinary units modulo squares is 3+9=12. These elements therefore span it.

The remaining six rows have absolute norms 8,343,13,169,169,169. At 13 each numerator vanishes at exactly one of the four distinct residue factors. The degree-one factor occurs for the element of norm 13 and each quadratic factor for a distinct element of norm 169. Together with the unique primes over 2 and 7 this certifies an explicit generator of each of the six prime ideals. Their six valuation parity vectors together with the twelve ordinary units give all eighteen dimensions of S-units modulo squares. In particular Cl(O_F[1/S])=Cl(F).

## The unit-supported Selmer calculation

Use the odd-degree hyperelliptic descent for the monic model of C. Its cohomology space H¹(K,J[2]) is the norm kernel in F*/F*², compatibly with localization. Finite points away from the branch locus map by X−θ, with the point at infinity as base divisor. Our rank comparisons use the standard Kummer subgroup J(K_v)/2J(K_v). General class-group bounds for this setting are treated by Barrera Salazar, Pacetti and Tornaría. [Schaefer, odd-degree descent](https://www.sciencedirect.com/science/article/pii/S0022314X8571044X) · [Barrera Salazar–Pacetti–Tornaría](https://arxiv.org/abs/2308.08663)

The S-unit square classes of K have dimension six. Norm onto this space splits by the inclusion of K because [F:K]=7 is odd. The projected elements g·N(F/K)(g) span the twelve-dimensional norm kernel on F's S-units. Their joint image at 2 and 13 is denoted G.

At the dyadic prime the defining septic is irreducible, so J(K₂)[2]=0. The local quotient has dimension 3[K₂:ℚ₂]=9, by the local abelian variety dimension formula. Nine points suffice. Their X-coordinates are

    1, 4, 12, 4ρ, 4(1+ρ), 4(2+ρ), 4(3+ρ), 4(1+2ρ), 12ρ.

The local square checks for X⁷+4⁶s⁷/ρ² succeed. Their nine images are independent. The first computation uses valuations and the multiplicative group modulo the fifteenth power of the unique prime over 2. The ramification index is 7, hence units congruent to 1 at depth 15 are squares by Hensel's lemma.

At 13 the local quotient has dimension three: there are four irreducible factors over the completion, giving three rational dimensions of J[2], and the residue characteristic is odd. Put d=1/(4ρ²). The three quadratics z²+bz+1 for b=3,5,6 are irreducible factors of z⁷−1 modulo 13. For a root β of one of their integral lifts in the unramified quadratic extension of ℚ₁₃, take X=4sβ over the corresponding quadratic extension of K₁₃. Here v(4s)=v(1+d)=1 in K₁₃, whereas v(β⁷−1)≥3. Thus X⁷+4⁶s⁷/ρ²=(4s)⁷(β⁷+d) has valuation eight. After dividing by a base uniformizer to the eighth power its residue comes from the nonzero elements of the base residue field, all squares in its quadratic extension. Hensel's lemma gives a point. Tracing its divisor down yields the square class of (θ/(4s))²+b(θ/(4s))+1. The three images are independent. Valuations and residual quadratic characters in the four completions compute them.

Let L be the direct sum of these local Kummer images. Exact binary linear algebra gives

    dim G = 12,     dim L = 9+3 = 12,     dim(G+L) = 23.

Thus among global norm-kernel S-units at most one dimension survives. The second calculation recovers the same ranks using the dyadic unit filtration and individual odd-place square tests. Divide by the uniformizer to record the valuation and raise the remaining unit to its seventh power to kill its residue without changing its square class. At odd depths j<15 use 1+c tʲ for c=1,ρ,ρ². At even depths below 14 use the squares of 1+c t^(j/2). At depth 14 use the squares with c=1,ρ and the additional element 1+t¹⁴. The program verifies that the eight products at each depth have all eight distinct leading residues; it then cancels these digits successively. Only 21 odd-depth bits and the last additional bit contribute unit square classes. These 22 generators span, and the first finite-group presentation also verifies the dimension. This supplies a second localization calculation without discrete logarithms at 2.

The point X₀=4s, Y₀=2⁶s⁴(ρ²+ρ−5) attains the bound. With the element d₅ supplied explicitly in verify_local.gp, the element u₀=s(t²+1)/d₅² is integral of absolute norm 13⁸ and X₀−θ=u₀(2d₅/t)². This S-unit class has nonzero local image. Since it comes from a global point it satisfies all further local conditions. The unit-supported Selmer subgroup therefore has dimension exactly one, and its generator is seen locally at the bad primes.

## Removing the unit restriction

The integral model has good reduction away from S since the polynomial discriminant is supported on S. This also follows from N(K/ℚ)(s)=13. At a good odd place the local Kummer subgroup is the unramified part of H¹(K_v,J[2]): multiplication by two is étale on the good model and the unramified group has the same order as J(k_v)/2J(k_v). In particular every Selmer class has even valuations in F outside S.

Mapping each such square class to the ideal obtained by halving its valuations outside S gives the usual map to Cl(O_F[1/S])[2]. Its kernel consists of S-unit square classes. The previous computation gives dim Sel₂ ≤ 1 + dim Cl(F)[2].

For the reverse inequality take all quadratic characters of the ordinary class group of F. By class field theory their quadratic extensions are unramified everywhere finite and split at the real places. All six primes in S are principal, so each extension splits at all six. The norm on square classes, equivalently corestriction on characters, gives a character of K unramified at every finite place and split at infinity. Indeed it is locally trivial at S, and elsewhere F/K is unramified and corestriction preserves unramified classes. Since K has class number one, that character is trivial. Each original character thus gives a norm-kernel class which is locally trivial at S and infinity and satisfies the unramified Kummer condition everywhere else. In the split norm-kernel description of J[2], unramifiedness may be checked after inclusion in the restriction of scalars of μ₂: that inclusion splits as Galois modules since seven is odd.

We have obtained dim Cl(F)[2] independent Selmer classes, all locally zero at S. The class of X₀ has nonzero localization there, so is independent of all of them. The lower and upper bounds now agree.

## Reproduction

Run with Python 3.8+ and PARI/GP (tested with 2.19.1). No conditional class-group routine is called by either certificate. The PARI program checks local squares, reductions and binary ranks. The pure Python program verifies the supplied units, valuations at 13 and quadratic-character independence.

    python3 verify_units.py
    python3 check_local.py /path/to/gp

The proof uses class field theory and odd-degree descent as cited above. Its field and local calculations are executable. The formula leaves a class-group parity question and relies on the separate Chabauty computation in Best–Dahmen–Freitas for any eventual application to all primitive solutions.
