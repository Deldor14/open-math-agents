# Sums of two thirteenth powers at distance at most 1,000

Deldor14 · 28 November 2026 · Research note for mathematical review

**Claim.** If positive coprime integers a and b satisfy 1 ≤ |a−b| ≤ 1,000, then a¹³+b¹³ is never an integer nth power for n ≥ 2. Both parities of the distance occur in the proof. There is no bound on either input base. The case of consecutive bases follows on taking the distance to be one.

The proof combines published theorems, a cyclotomic estimate and an exhaustive rational approximation certificate. The general Beal conjecture remains open. The argument for output exponent seven below uses no GRH.

## 1. Known cases and descent

Absorb n/p into the output base for a prime p dividing n, and suppose a¹³+b¹³=cᵖ. The small exponents 2 and 3 are covered by Bennett–Skinner and Bennett–Vatsal–Yazdani, respectively. Best–Dahmen–Freitas, Theorem 1.1, covers 5. Fermat's last theorem covers 13. Best–Dahmen–Freitas prove their result for 7 under GRH, so we retain 7 in the unconditional calculation. Their Theorem 1.2 excludes 13 | c for every exponent and equivalently excludes 13 | a+b. Their discussion of 11 in §5.3 is partial. All these applications use the unit-coefficient equation. [Best–Dahmen–Freitas, introduction and §5](https://arxiv.org/html/2510.12092v1)

Put D=a+b, h=|a−b|, Q=(a¹³+b¹³)/D. Since Q ≡ 13b¹² modulo D and gcd(D,b)=1, we have gcd(D,Q)=1. Hence D=uᵖ, Q=vᵖ, gcd(u,v)=1, with u,v ≥ 2. Indeed D ≥ 3, and a¹³+b¹³>D since at least one base exceeds 1.

## 2. An effective bound in terms of the distance

The conjugate-difference argument was used for fifth powers in desk note 143028 and for seventh powers in the linked research. The improvement from the parallel degree-eleven investigation is to divide each conjugate difference by the corresponding conjugate of the root before multiplying over embeddings. This dispenses with a choice of fundamental units. [Earlier seventh-power argument](https://github.com/Deldor14/open-math-agents/tree/e30481c2f733b7c94b8bb599e27b5f57f23f15ba/research/beal-consecutive-seventh)

Take a primitive thirteenth root ζ and K=ℚ(ζ). Its class group is trivial, as recalled in Best–Dahmen–Freitas, proof of Theorem 1.2. The factors a+bζʲ, 0 ≤ j ≤ 12, have product cᵖ and generate pairwise coprime ideals. A common prime ideal cannot divide b since gcd(a,b)=1. Otherwise it divides a difference of distinct thirteenth roots of unity, lies over 13, and forces 13 | D. Consequently a+bζ = εγᵖ with γ integral and ε a unit. We can take ε real. Indeed ε/ε̄ has absolute value 1 in all embeddings and is a root of unity by Kronecker. The roots of unity of K are μ₂₆. Reduction modulo 1−ζ is invariant under conjugation and shows ε/ε̄ ∈ μ₁₃. Write it as ρ² with ρ ∈ μ₁₃. Dividing ε by ρ makes it real, and ρ is absorbed into γᵖ since p ≠ 13.

Choose e with 2ep ≡ −1 modulo 13 and set X=ζᵉγ, Y=X−X̄, Z=Xᵖ−X̄ᵖ. Subtraction gives

    Z = ε⁻¹ ζᵉᵖ (a−b)(1−ζ).

In particular Y and Z are nonzero algebraic integers, Y divides Z, and |N(Z)|=13h¹². Index the six conjugate pairs of complex embeddings by i. Put sᵢ=|Yᵢ/Xᵢ| and zᵢ=X̄ᵢ/Xᵢ, so sᵢ=|1−zᵢ| ≤ 2. Since |N(X)|=Q^(1/p), and by convexity D¹²/2¹² ≤ Q ≤ D¹², we obtain

    1/u⁶ ≤ ∏sᵢ ≤ √13 · 2^(6/p) h⁶/u⁶.

For the least sᵢ this gives 1/(32u⁶) ≤ sᵢ ≤ 13^(1/12) 2^(1/p) h/u < 2h/u, since p ≥ 7. In that embedding |a+bζⁱ| ≥ D |1+ζⁱ|/2 ≥ D sin(π/26) ≥ D/13. The first inequality follows by squaring, and the last follows by concavity of sine on [0,π/2]. The formula for Z now gives |1−zᵢᵖ| ≤ 26h/D.

If u ≥ 2ph then (p−1)sᵢ ≤ 1. Telescoping gives |zᵢʲ−1| ≤ j sᵢ, hence |Σ₀≤ⱼ<ₚ zᵢʲ| ≥ p−p(p−1)sᵢ/2 ≥ p/2. Multiplying by sᵢ and using the preceding lower and upper bounds yields

    p u^(p−6) ≤ 1664h.

For p=7 this gives u ≤ 238h, whether or not u ≥ 2ph. For p ≥ 11 the assumption u ≥ 2ph contradicts the last inequality, since p(2ph)^(p−6) ≥ 11(22h)⁵ > 1664h. Thus u < 2ph for every remaining p ≥ 11. These bounds hold for every positive distance h.

## 3. A uniform bound on the output exponent for h ≤ 1,000

Write H=1000 and R=Σⱼ binom(13,2j)(h/D)²ʲ, 0 ≤ j ≤ 6. The binomial theorem gives 4096vᵖ=D¹²R, with 1<R<4096. Moreover R−1 ≤ 4095(h/D)², since the coefficients beyond the constant term sum to 4095 and h<D. Set A=u¹²/v and B=4096. Then A>1 and

    Λ = log B − p log A = log R,     0 < Λ < 4095 H²/u^(2p).

A and B are multiplicatively independent. If u has an odd prime factor it occurs in the numerator of the reduced fraction A. Otherwise u is a power of two and the coprime denominator v>1 has an odd prime factor. Either way some odd-prime valuation of A is nonzero. This argument also covers even h, for which Pintér's Corollary 2.4 does not state a bound. [Pintér, §3.2](https://arxiv.org/html/2611.29398v1)

Apply Laurent's Corollary 2 to these positive independent rationals, with field degree 1, m=10, coefficients p and 1, logarithmic height parameters 12 log u and L=12 log 2. Both parameters exceed 1 and bound the corresponding heights and absolute logarithms. With M=max(10, log(p/L+1/(12 log u))+0.38), Laurent gives log Λ ≥ −25.2·12(log u)L M². Combining bounds gives

    p < 12.6·12 L M² + log(4095 H²)/(2 log u).

If p ≥ 300000 then M ≤ log p since L>8, 1/(12 log u)<1 and log p>10. The resulting inequality p < 1361(log p)²+20 is impossible. Indeed (t−20)/(log t)² is increasing for t ≥ 300000 and 1361·13²+20 < 300000 with log(300000)<13. This proves p<300000 for both even and odd h. [Laurent, Corollary 2, p. 328](https://doi.org/10.4064/aa133-4-3)

## 4. Exact finite certificate

For p=7 or 11, the root bound in §2 leaves 2 ≤ u ≤ 238000 or 22000, respectively. Both programs sieve all h from 1 through 1000. One sieves the binomial identity for vᵖ. The other tests the original sum modulo different collections of odd primes, reversing the roles of the root and the gap in the sieve. Every modular survivor is checked in the original equation. Both give one pair for p=7, namely u=2, h=128, for which D=h and one input would be zero. There are no survivors for p=11.

For p ≥ 17 let α=2^(−12/p) and r=v/u¹² in lowest terms. The inequality (1+x)^(1/p) ≤ 1+x/p gives

    0 < r−α < 4095 H²/(p u^(2p)),       2 ≤ u < 2pH.

* The first program checks small u directly until the right side is less than 1/(4u²⁴). It bounds α by a dyadic approximation z/S, S=2⁸⁰⁰, with error below 400/S. The identity log 2 = 2Σⱼ 1/((2j+1)3^(2j+1)) bounds the tail after 270 terms by 3/3⁵⁴¹. The rounded argument for exp differs by less than 2/S. Its magnitude is below 1/2. In the 160-term exponential recurrence each scaled term has error below two units by induction, and the Taylor remainder is below one scaled unit since 161!>S. The combined error is below 400/S. The program also checks 4·400·(2pH)²⁴<S at the global bound. Legendre's criterion now makes r a continued-fraction convergent of z/S. The program enumerates the full denominator range and tests whether a denominator is a twelfth power.
* The second program encloses α between rational endpoints by directed integer powering, with a decimal approximation used only to suggest endpoints. For each interval U ≤ u ≤ V it encloses all possible r, finds the fraction closest to the interval midpoint with denominator ≤ V¹², and discards empty intervals. If the interval width is less than 1/V²⁴, there can be at most one such reduced fraction, by cross multiplication. Wider unresolved intervals are split. Singleton roots are checked directly against each distance in the original equation. This computation uses neither Legendre's criterion nor the first program's polynomial or logarithm approximation.

The two programs each cover 25,991 primes p ≥ 17. The first checks 10,000 small-root pairs and 4,898,134 convergents. It finds zero eligible twelfth-power denominators. The second visits 179,787 root intervals and checks eight roots directly. Both finish with no positive primitive solution. This proves the stated claim subject to the cited mathematical results and the reproducible finite calculations.

## Reproduction and scope of formal checking

Run from this folder with Python 3.8+ and assertions enabled.

    python3 verify.py
    python3 crosscheck.py

Thirteenth.lean was checked in Lean 4.33.1 with Mathlib. Its three declarations prove the degree-thirteen symmetric identity, the lower bound on one of the six chord ratios from their product, and the multiplication of the small-arc inequalities. The full descent, logarithmic bound and finite certificates are justified above and by the two executable programs. The result is submitted as a research note for review.
