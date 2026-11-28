# Prime divisors of primitive quintic sums

Suppose a,b,c are positive integers with gcd(a,b)=1 and a⁵+b⁵=cᵖ for a prime p≥7. The following restrictions have no upper bound on p.

1. If p≢1 mod 5, then p∤c.
2. If a prime q|c has q≡−1 mod 5, then q≡−1 mod p. If q≡2 or 3 mod 5, then q²≡−1 mod p. In particular, when p≡3 mod 4, every prime factor of c is 1 or −1 mod 5.
3. The product ab is divisible by **1218 = 2·3·7·29**. When p≥59, it is divisible by **1,316,658 = 2·3·7·23·29·47**.

These are deductions from existing modularity theorems. The first two statements use no numerical sieve. The third uses point counts on five small finite fields and their quadratic extensions. The argument gives necessary conditions and does not establish the full Beal conjecture. Priority has not been established. For a multiple of a prime p as original exponent, apply the assertions to the corresponding power of c.

## Modular inputs and the reference Jacobian

Put F=ℚ(√5), B=J₅(a,b), and A=J₅(0,1), the Jacobian of y²=x⁵+1. The full rational Tate module over F decomposes into two-dimensional real-multiplication blocks after extending coefficients. Billerey, Chen, Dieulefait and Freitas (BCDF) prove that at each coefficient prime above p the residual representations of B and A agree up to a quadratic character. In section 12 they give an untwisted comparison for the normalized solution obtained by changing signs and interchanging a,b. The Frey Jacobian has multiplicative reduction at each prime above q|c, q∤10. The primes 2 and 5 do not divide c, since for either prime divisibility of a⁵+b⁵ is equivalent to divisibility of a+b and BCDF exclude those cases. [BCDF, Theorem 1.8, Theorem 3.11, Proposition 5.14 and section 12](https://arxiv.org/pdf/2205.15861) · [BCDF, Theorems 5 and 6](https://arxiv.org/pdf/1703.06530).

For a residue field of size Q≡−1 mod 5 in characteristic different from 2 and 5, Frobenius on A squares to −Q on the full characteristic-zero Tate module (auxiliary Tate prime different from the residue characteristic). Indeed the order-five automorphism on x has four distinct, one-dimensional eigenspaces, and the Weil pairing pairs opposite eigenspaces. Frobenius swaps each such pair and acts on the pairing by Q, so on the pair its trace vanishes and its determinant is Q. Each two-dimensional real-multiplication block therefore also has trace zero: its determinant is Q and its Frobenius square is −Q.

## The exponent prime

The following local argument deals with the prime equal to the exponent, where the usual level-raising test away from p does not apply.

Suppose p≢1 mod 5 and p|c. Take a place of F above p. Its residue degree h is 1 for p≡4 mod 5 and 2 for p≡2,3 mod 5, hence Q=pʰ≡−1 mod 5. The abelian surface A has good reduction. Over the field of size Q²ⁿ its special fiber has (1−(−Q)ⁿ)⁴ points by the preceding Frobenius calculation. These orders are all prime to p. Every geometric p-torsion point would be defined over one of those fields, so the reduction has p-rank zero and its finite p-torsion group scheme is geometrically connected.

For completeness, consider the full mod p representations on A[p] and B[p]. The comparison on all two-dimensional blocks gives equal semisimplifications after removing the quadratic twists: reduction of a stable lattice has lattice-independent composition factors, and one can take the direct sum over the embeddings of the real multiplication field. Restriction to a local Galois group preserves equality of composition factors. If using the twisted statement of Theorem 1.8, pass to the compositum of the local quadratic extensions cutting out the characters of the two blocks. There are at most two characters, with values ±1, so the ramification index is at most 4. Any further unramified extension keeps that bound. The base field F at p is unramified over ℚₚ, so throughout we have absolute ramification index e<p−1. Equality after extension of coefficient scalars also yields equality of the full ℱₚ-semisimplifications by Brauer–Nesbitt.

The semistable variety B has positive toric rank. After an unramified extension its uniformizing period lattice is constant. The exact sequence from Raynaud uniformization gives B[p] a quotient Y/pY, where Y is that lattice of positive rank. In particular the trivial one-dimensional mod p character is a composition factor, and hence also a composition factor of A[p]. [Uniformization exact sequence, Proposition 2.14](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.1151.pdf).

This is impossible for A. Take the schematic closures of a generic-fiber composition filtration inside its finite flat p-torsion over the valuation ring. Each subquotient is finite flat. By Raynaud's full faithfulness for e<p−1, the subquotient with trivial one-dimensional generic fiber must be the constant group scheme ℤ/p. Its special fiber is étale and disconnected. Every subgroup of the geometrically connected special fiber of A[p] is geometrically connected, since a quotient ring of a local Artinian ring is local. Every quotient of such a subgroup is also geometrically connected. The special fiber therefore cannot have the stated subquotient. This proves p∤c. [Raynaud, corollaire 3.3.6](https://www.numdam.org/item/10.24033/bsmf.1779.pdf).

## Prime divisors away from the exponent

Let q|c be a prime with q≢1 mod 5. The preceding argument, together with the exclusions at 2 and 5, allows us to assume q∤10p. A place v of F above q has norm Q=q when q≡−1 mod 5 and Q=q² when q≡2,3 mod 5. In both cases Q≡−1 mod 5. At this place the multiplicative reduction of B gives the level-raising test a_v(A)²≡(Q+1)² modulo the coefficient prime above p, after the normalization of BCDF. The trace computed above is zero, so p|Q+1. When p≡3 mod 4, −1 has no square root modulo p, which excludes q≡2,3 mod 5. [BCDF, section 9.7](https://arxiv.org/pdf/2205.15861).

## Fixed divisors of ab

BCDF give 2|ab. At q=3,7,29 the preceding restrictions rule out q|c for every p≥7: q²+1 is 10 or 50 for q=3 or 7, and q+1=30 for q=29. The equal-prime cases are covered by the argument at p. Likewise q=23,47 cannot divide c for p≥59, as q²+1 is 530=2·5·53 or 2210=2·5·13·17.

For the good-prime trace tests take q≠p from this list. Then q∤D=a+b. Write x=a/D modulo q and scale to the pair (x,1−x). Scaling both parameters changes the displayed curve only by a quadratic twist: substitute D times the coordinate in the polynomial below and factor out D⁵. Switching a,b or negating both parameters likewise gives at most a quadratic twist by x↦−x in the curve coordinate. Thus vanishing of a trace modulo p, and the traces of squared Frobenius, are invariant under these operations.

On the normalized pair (u,v)=(x,1−x) use the Frey curve

    y² = t⁵ + 5uv t³ + 5u²v² t + v⁵ − u⁵.

Let T₁ and T₂ be q+1−#C(ℱ_q) and q²+1−#C(ℱ_{q²}). For q=3,7,23,47, the modular comparison at the degree-two place requires T₂≡0 mod p. For q=29 it requires T₁≡0 and T₂≡−4q modulo p: the two reference blocks have trace zero and Frobenius square −q. These requirements follow on the full Tate module by combining the two blocks. A quadratic sign disappears on squaring Frobenius. The model and its good reduction are given in BCDF (5.1) and Proposition 5.15.

Enumerating all x gives the following results. In each row the obstruction value is zero exactly at x=0,1.

| q | Obstruction | Remaining nonzero values or bound |
| --- | --- | --- |
| 3 | T₂/2 | −4 |
| 7 | T₂/2 | −12, −6, 4 |
| 29 | gcd(T₁,T₂+4q) | 2, 4, 6, 8, 12, 40, 160 |
| 23 | T₂/2 | even and of absolute value at most 44 |
| 47 | T₂/2 | even and of absolute value at most 90 |

For 3,7,29 no nonzero obstruction has a prime divisor ≥7. For 23 and 47 no nonzero obstruction has a prime divisor ≥59. The necessary congruences force x=0 or 1, hence q|ab. At p=q=7 the full signature is already excluded by Dahmen and Siksek. At p=q=29 the previously certified cyclotomic calculation gives 29²|ab, without assuming GRH. This proves the product assertions. [Dahmen and Siksek, Theorem 1](https://www.few.vu.nl/~sdn249/SumsOfPowers.pdf) · [Cyclotomic calculation](CyclotomicDescent.md).

Run `python3 verify_small_frobenius.py` to reproduce the five rows. For every polynomial value over the quadratic extension the program tests squareness both by its norm and by enumerating squares. The mathematical deductions in this note are written proofs; the script checks the finite tables.
