# Auxiliary primes and square lifts for the quintic Beal branches

The branch 5 dividing a+b is already excluded by Billerey, Chen, Dieulefait and Freitas, Theorem 5 of [their multi-Frey paper](https://arxiv.org/pdf/1703.06530). For restrictions on the remaining branch across 33 prime exponents, see [the cyclotomic descent](CyclotomicDescent.md).

## Primitive integer obstruction

Let a,b,c be positive integers, gcd(a,b)=1, and suppose a⁵+b⁵=cʳ. For 5 dividing a+b the following implications hold for every positive integer exponent r:

| Divisor of r | Required divisor of a+b |
| --- | --- |
| 11 | 23ʳ |
| 29 | 59ʳ |
| 113 | 227ʳ |

For every positive multiple r of 29, **59 divides abc irrespective of whether 5 divides a+b**. These are necessary conditions on a hypothetical primitive solution. The theorem `BealForcedPrimes.primitive_forced_primes` proves the three implications starting with the original power equation. The theorem `BealForcedPrimes.divides_product_59` proves the assertion without the condition at 5. This work makes no priority claim.

Here is the mechanism. Put D=a+b and Q=(a⁵+b⁵)/D. For any prime dividing D, reduction gives Q≡5b⁴ modulo that prime. When 5 divides D, write D=5h and Q=5g. Expansion gives

    g = b⁴−10hb³+50h²b²−125h³b+125h⁴ ≡ b⁴ modulo D.

Thus gcd(5D,g)=1. Taking r-th roots of the two coprime factors of cʳ gives 5D=sʳ and Q=5tʳ. In the other branch gcd(D,Q)=1, giving D=sʳ and Q=tʳ. Write k=5 or 1 respectively. At any auxiliary prime ℓ not dividing 5D take W=(a−b)/D and T=t/s⁴. Expansion gives

    5W⁴+10W²+1 = 16 k⁵ Tʳ.

For ℓ=2e+1 prime and e dividing r, Tʳ is one of 0,1,−1 modulo ℓ. For (e,ℓ)=(11,23),(29,59),(113,227) the polynomial on the left attains none of 0, ±16·5⁵. Thus ℓ divides D in the k=5 branch. As sʳ=5D, ℓʳ divides D. Moreover 5 also divides s, so (5ℓ)ʳ divides 5D. In the k=1 branch, modulo 59 the only W giving 0 or ±16 are W=±1. If 59 does not divide D this forces 59 to divide a or b. If 59 divides D it divides c. The finite residue tables are proved by Lean's kernel.

## Rational lift and checked congruences on multiples

For signed rational summands a,b with a+b≠0 put U=(a²+b²)/(a+b)². Then 5U²=1+4k⁵Tʳ and 2U−1=W². Conversely a rational W gives normalized summands (1+W)/2 and (1−W)/2, and the displayed curve equation recovers their cofactor. Reconstructing primitive integers requires the correct denominator branch.

For r=3 this gives the familiar elliptic quotients in Poonen's proof. In short coordinates they are

| Elliptic curve | Condition for a rational lift | Generator |
| --- | --- | --- |
| Y²=X³+2000 | Y/50−1 is a rational square | P=(20,100) |
| Y²=X³+80 | Y/10−1 is a rational square | P=(4,12) |

The rational equivalences in both directions are checked in `BealQuintic.lean`. Poonen proved the complete primitive signature (5,5,3) in 1998. The following reproducible calculation supplies necessary congruences on the index n in an affine point nP that lifts. The integer n is an elliptic-curve index, not an original base or exponent.

- On Y²=X³+2000, n is 0 or 1 modulo **85446462664812688639200**.
- On Y²=X³+80, n is 0 modulo **15344475765347062625827536000**.

The generator and trivial torsion identifications use Cremona's tables. Their minimal curves have coefficients [0,0,1,0,31] and [0,0,1,0,1] and generators (5,12) and (1,1), respectively. The change X=4x, Y=8y+4 gives the displayed models.

To replay the certificate, run `python3 verify_beal_multiples.py` with `BealMultiples.json` beside it. At each listed good prime ℓ>5 the verifier finds the local order by repeated elliptic curve addition. If nP is finite after reduction, the rational square condition implies the corresponding residue is a square, including zero. If nP reduces to infinity the verifier keeps that class unconditionally. Each local order divides the period being certified. Each stage enumerates every lift of every surviving class from the previous period. The two certificates use 95 and 87 distinct good primes, respectively. This finite computation does not eliminate all indices in the remaining classes.

## Sources

- Bjorn Poonen, section 4 of *Some Diophantine equations of the form xⁿ+yⁿ=zᵐ*, on the classical (5,5,3) case and rational quotients: https://matwbn.icm.edu.pl/ksiazki/aa/aa86/aa8631.pdf
- John Cremona's generators and torsion data, rows 675 a 1 and 225 a 1: https://github.com/JohnCremona/ecdata/blob/master/allgens/allgens.00000-09999
- Problem and earlier team reductions: https://lefttosolve.com/p/BealConjecture.beal_conjecture
- The prize for the full conjecture: https://www.bealbank.com/who-we-are/our-founder/the-beal-conjecture/
