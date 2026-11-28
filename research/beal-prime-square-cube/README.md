# A conductor bound for Beal's prime-output square–cube family

Let p be an odd prime, k ≥ 3, and U,V positive coprime integers with U² + V³ = pᵏ. The following four ranges, including all their exponents and heights, have a single joint list of exceptions.

| Hypothesis | Upper bound on p |
|---|---:|
| All U,V | 578 |
| 9 divides U | 1736 |
| 4 divides V | 18518 |
| Both 9 divides U and 4 divides V | 55555 |

| p | k | U | V |
|---:|---:|---:|---:|
|19|5|654|127|
|71|3|588|23|
|71|4|4785|136|
|113|7|15312283|9262|
|193|3|2355|118|
|349|3|6216|157|
|443|3|9324|11|
|1777|4|3085855|7656|

Only rows meeting the hypothesis and bound of a particular range belong to that range. Each displayed identity holds, and at least one of the ranges includes each row. The eight values of U have, respectively, prime divisors 2,3,5,7,3,3,7,5 to valuation exactly one.

Consequently a primitive positive equation aˣ + bʸ = pᵏ with x,y,k > 2, 2 dividing x, and 3 dividing y is impossible in any of these ranges. Put U = a^(x/2) and V = b^(y/3). Since x/2 ≥ 2, a value of U in the table cannot occur. The conclusion also holds with the two summands interchanged, including when an input base is 1. The condition 9 dividing U can equivalently be written 3 dividing a.

## Why the finite computation covers unbounded inputs

For p ≥ 5 consider E given by y² = x³ + 3Vx + 2U. Its invariants are c₄ = −144V, c₆ = −1728U and Δ = −1728pᵏ. At p the curve has multiplicative reduction since p does not divide V. It has good reduction away from 2,3,p. The quadratic twists used below preserve these properties and preserve the ratio c₄³/c₆² = −V³/U². Since U,V are coprime, reducing this ratio recovers V³ and U² exactly.

At 2, a twist by one of ±1,±2 has conductor exponent at most 5. The local computation is Table 1 of Freitas, Naskręcki and Stoll, using a = ±U and b = V; the sign of U exchanges quadratic twists. For these odd right sides U,V have opposite parity, so rows 3–11 apply. In the table the conductor column gives the local conductor, independently of the subsequent level-lowering test. This includes row 11. Every row in question allows a twist in ±1,±2. The local condition that the right side is a prime-exponent power there imposes no restriction on a 2-adic unit, since raising to an odd power is an automorphism of the unit group. [Freitas–Naskręcki–Stoll, §3, Table 1](https://www.mathe2.uni-bayreuth.de/stoll/papers/genfermat-export.pdf)

At 3 the discriminant has valuation 3. A twist by ±1 or ±2 is unramified or trivial locally at 3. Ogg's conductor formula gives conductor exponent at most 3. When 9 divides U, the displayed short model is minimal at 3, with singular point at the origin and a₆ = 2U divisible by 9. In Tate's algorithm the type-II test fails. The reduction is additive, hence has at least two geometric components, so Ogg's formula gives exponent at most 2. This also agrees with row 3 of Table 2 in the same paper. [Tate, Algorithm for determining the type of a singular fiber](https://wstein.org/Tables/antwerp/tate/tate.pdf)

When 4 divides V, choose the sign U′ = ±U with U′ ≡ 1 modulo 4. The integral model y²+y = x³+(3V/4)x+(U′−1)/4 has discriminant −27pᵏ. Its invariants are c₄ = −36V and c₆ = −216U′, so it has the same invariant ratio and good reduction at 2. It is a quadratic twist of E, with twisting factor ±2 up to squares; this also follows by completing the square and scaling. Thus the four upper bounds for the conductor are 864p, 288p, 27p and 9p. Each bound in the first table places a suitable curve within the complete conductor range through 499999. The case p = 3 is covered separately by the complete good-reduction catalogue for {2,3} described below.

## Catalogue and independent checks

Cremona's complete conductor tables supply all 3,064,705 rational isomorphism classes in the 50 published blocks. The manifest in this directory records the byte length and Git blob identifier of every block. The verifier cremona.py checks them before scanning all rows; it processes the 192810 rows whose conductor is 2^i 3^j p with p ≥ 5 prime, i ≤ 6 and j ≤ 3. It reduces the invariant ratio and tests the extracted integers with exact powers. For a separate calculation pari_audit.py sends the original five Weierstrass coefficients to PARI/GP, first discarding only levels supported on 2 and 3. For levels with one other prime appearing exactly once, PARI computes the invariant J = j(E)/1728. It tests whether the reduced denominator is pᵏ, the numerator is a positive cube, and the numerator of 1−J is a square. The two computations give precisely the eight rows above. [Cremona catalogue](https://johncremona.github.io/ecdata/) · [Pinned source files](https://github.com/JohnCremona/ecdata/tree/6fedd3ab463a70e52061ebc0b04832ad19fd2e01/allcurves)

Independently, for all 37 odd primes through 163, the catalogue of von Känel and Matschke includes all curves with good reduction outside {2,3,p}, since the product of these places is at most 1000. The two programs classify.py and check_scales.py recover precisely the first four rows from 177248 curve records. The second program uses the minimal invariants directly. If the short model above is obtained from a minimal model with scale s, then its integral invariants are s⁴c₄ and s⁶c₆. Coprimality of U,V gives s = 1 or 2. At 3 one of the two valuations is at most 2 or 3 respectively, and at primes ≥5 one valuation is zero. At 2, at least one is exactly 4 or 6 respectively. The program checks the individual section sizes against the authors' numberOfCurves.txt. Completeness here uses §4.2.5 of the authors' paper. [Paper](https://arxiv.org/abs/1605.06079) · [Data and download links](https://bmatschke.github.io/solving-classical-diophantine-equations/)

The compiled file Identities.lean verifies the invariant identities, the eight equalities and the eight obstructions to U being a perfect power. The arguments about conductors and the two published curve enumerations enter the written proof externally. The point of the computation is exhaustion under the stated bounds. Individual identities, including the one at 113, were known. Bennett and Siksek already covered the cubic-root input for primes below 100, as well as even output exponents for primes below 1000. [Bennett–Siksek, §2 and Theorem 5](https://personal.math.ubc.ca/~bennett/BeSi-ANT-2023.pdf)

### Reproduction

Use the 50 pinned allcurves files, collected in one directory, and the authors' curves_maxNS_1000.txt and numberOfCurves.txt. No database files need modification.

```sh
python3 cremona.py /path/to/allcurves cremona-files.tsv
python3 pari_audit.py /path/to/allcurves /path/to/gp
python3 classify.py /path/to/curves_maxNS_1000.txt 163
python3 check_scales.py /path/to/curves_maxNS_1000.txt /path/to/numberOfCurves.txt
lake env lean Identities.lean
```
