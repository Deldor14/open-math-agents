# A relative separation bound for sums of two thirteenth powers

Deldor14 · 28 November 2026 · Research note for mathematical review

**Claim.** Let a and b be distinct positive coprime integers, D=a+b and h=|a−b|. If a¹³+b¹³ is an integer perfect power of exponent n≥2, then

    h > 1000    and    h¹⁶⁰⁰⁰ > D.

In addition, if n has a prime divisor p≥16000 then D < (64h)³². The first strict inequality was established in the previous bounded-gap note. The relative inequality excludes gaps growing with the height, with no cutoff on a, b, or h. These are necessary conditions in a restricted signature of the open Beal conjecture. [Bounded-gap proof, including the cyclotomic root estimates](https://github.com/Deldor14/open-math-agents/tree/6114e9176809d944e377e9df6f580ddc1abf2831/research/beal-thirteenth-gap)

## Two logarithms with base two

Take a prime divisor p of n and absorb n/p into the output base. The previous note applies the small-exponent results and the ramification theorem of Best–Dahmen–Freitas. In the cases left, p is 7, 11 or at least 17, D=uᵖ, and (a¹³+b¹³)/D=vᵖ with u,v coprime integers at least two. It proves u≤238h for p=7 and u<2ph for p≥11. These two estimates apply for every h. [Best–Dahmen–Freitas](https://arxiv.org/html/2510.12092v1)

Put A=u¹²/v>1. The binomial identity in the previous note gives the positive linear form

    0 < Λ = 12 log 2 − p log A < 4095 h² / u^(2p).

The reduced positive rational A has some nonzero valuation at an odd prime, so A and 2 are multiplicatively independent. We use Laurent's Corollary 2 with m=10, field degree one, coefficients p and 12, and logarithmic height parameters 12 log u and 1. This choice reduces the coefficient in the exponent bound. Writing M=max(10,log(p+1/log u)+0.38), we obtain

    (1)   p < 151.2 M² + log(4095 h²)/(2 log u).

This follows by bounding log Λ below by −25.2·12(log u)M² and above by log(4095 h²)−2p log u. [Laurent, Corollary 2, p. 328](https://doi.org/10.4064/aa133-4-3)

For p≥16000, M≤log p+0.4. The ratio (log t+0.4)²/t is decreasing for t≥16000, by differentiation. Since log(16000)<9.7 and 151.2·10.1²<(31/32)16000, it follows that 151.2M² < (31/32)p. Substitution into (1) gives D^(1/32)<√4095 h<64h. This proves the high-exponent assertion for all gaps.

## Relative gaps at any output exponent

Suppose hᴷ≤D with K=16000. Substitution into (1) gives

    (1−1/K)p < 151.2 M² + 7,

since log(4095)/(2 log u)<7. For p≥15400, M≤log p+0.4. At t=15400, log t<9.65 and 151.2·10.05²+7 < (1−1/K)15400. Both (log t+0.4)²/t and 7/t decrease beyond that point. Thus p<15400.

If p≤6000 then u≤12000h, also for p=7. Therefore h¹⁶⁰⁰⁰≤(12000h)⁶⁰⁰⁰ and h⁵≤12000³. Since 1000⁵>12000³, this contradicts h>1000 from the preceding note.

It remains to exclude the primes 6000<p<15400. Since u<2ph and h≤u^(p/K), we have u<(2p)^(K/(K−p)). Set U=(2p)^ceil(K/(K−p)) and Q=U¹². The reduced fraction r=v/u¹² has denominator ≤Q. With α=2^(−12/p), concavity of the pth root and the binomial identity give

    0 < r−α < (4095/p) u^(−2p+2p/K) < 2^(2−2p).

Here u≥2, p>6000 and p<K. The verifier takes a dyadic scale S satisfying 2^(2−2p)<1/S. It proves by outward-rounded integer powers that (g−1)/S < α < (g+2)/S for an integer g. Thus r belongs to the interval [(g−1)/S,(g+3)/S].

For each prime it exhibits rational bounds A₀/B₀ < (g−1)/S ≤ (g+3)/S < C₀/D₀ with B₀C₀−A₀D₀=1 and B₀+D₀>Q. Any intervening fraction m/n with positive denominator would satisfy

    n = B₀(C₀n−D₀m) + D₀(B₀m−A₀n) ≥ B₀+D₀.

Both parenthesized integers are positive. This excludes every possible r. Decimal arithmetic and the nearest-fraction routine suggest candidate endpoints only. The ordering, unit determinant, denominator sum and power comparisons are all verified with integer arithmetic. FareyGap.lean proves the displayed denominator inequality in Lean 4.33.1.

The verifier covers all 1,016 primes in the indicated interval. Its largest dyadic scale is 9,694 bits and no interval admits an eligible denominator. Run with Python 3.8 or newer and assertions enabled.

    python3 verify_height.py

The strict relative inequality follows. The cyclotomic and logarithmic parts are written arguments, with the cited literature and the bounded-gap certificate as dependencies.
