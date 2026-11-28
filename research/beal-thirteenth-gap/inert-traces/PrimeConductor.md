# An explicit boundary trace at every odd prime conductor greater than three

Deldor14. Written lemma for review. This computes the trace ingredient in the
cyclotomic approach to signatures `(l,l,p)`. Divisibility in a Jacobian,
global units, and the preceding reduction to a curve are separate hypotheses
in applications to the generalized Fermat equation.

Let l ≥ 5 be prime, z a primitive l-th root of unity, H its maximal real
subfield, x = z + z⁻¹, and xⱼ = zʲ + z⁻ʲ. Put W = x(x−2) and
F(x) = x⁻¹ + 3x⁻² + 2x⁻³. These are algebraic integers since
x = z⁻¹(1+z²) is a unit. These factors arise by taking d₁=4−x²
and d₂=2−x. With R=d₂/d₁, U=R(R−1) and Y₀=2R−1 one has
W=2d₂−d₁ and F(x)=U/Y₀³.

## The trace table

For 1 ≤ j ≤ (l−1)/2, write Tⱼ = Tr(H/Q)(xⱼ(xⱼ−2) F(x)).
Then Tⱼ = l Sⱼ, where the following table gives **4Sⱼ**.

| j modulo 4 | l ≡ 1 modulo 4 | l ≡ 3 modulo 4 |
|---|---|---|
| 0 | −j² | j² |
| 1 | 3j²−2lj−5 | −j²−2lj+12j−5 |
| 2 | 2l²−3j²+12l−12j+10 | −2l²+3j²+12l−12j−10 |
| 3 | j²+2lj+12j+5 | −3j²+2lj+5 |

Each entry is divisible by four for the indicated residue classes.
None is zero. In both columns the signs in rows 1, 2, 3 (indexed by
the residues) follow from 1 ≤ j < l/2, except possibly in row 2 of
the right column. There, for l ≥ 11, use
−2l²+3j²+12l < −5l²/4+12l < 0. At l=7, j=2 gives −36.
For row 1 on the right, l ≥ 7 makes 12−2l negative.
In every case |Sⱼ| ≤ (l+1)(l+5)/2. For the odd rows use
3j²+2lj+12j+5 < 2l²+12l+10. For row 2 use its known sign
and j < l/2 in the displayed entries.

### Calculation

Use all l-th roots t of unity, including 1, and set

    Cᵣ(k) = (1/l) ∑ tᵏ (t+t⁻¹)⁻ʳ,       C = C₁+3C₂+2C₃.

The denominator never vanishes. The t=1 term drops out of the trace of
WⱼF, and the remaining sum counts each real embedding twice. Since
C(k)=C(−k), expansion of Wⱼ gives Tⱼ/l = C(0)+C(2j)−2C(j).

For each r=1,2,3 let mᵣ be the least nonnegative solution of
2mᵣ ≡ −k−r modulo l. The three values are

    C₁(k) = (−1)^m₁ / 2,
    C₂(k) = (−1)^m₂ ((m₂+1)/2 − l/4),
    C₃(k) = (−1)^m₃ ((m₃+1)(m₃+2)/4 − l(2m₃+3)/8).

Indeed, expand t^(k+r)/(1−a t²)^r for |a|<1, then average over t.
Only the terms m=mᵣ+lh survive, with coefficients binom(m+r−1,r−1).
Evaluate the resulting rational functions at a=−1. With q=a^l=−1,
the rational continuations of ∑qʰ, ∑h qʰ, ∑h² qʰ for h≥0 have values
1/2, −1/4, 0 respectively. This proves the three identities.

To obtain the table use these formulas at k=0,j,2j. For k+r even one
may take mᵣ=l−(k+r)/2. For k+r odd one may take mᵣ=(l−k−r)/2.
The latter expression can give −1 at the endpoint. Its extra binomial
coefficient is zero there (r ≥ 2), so it gives the same rational sum.
The parities of all nine mᵣ in these substitutions depend only on l and j
modulo 4. In particular the resulting identities are quadratic polynomials
on each of the eight cells. The accompanying code additionally checks
them by exact interpolation with six unisolvent points per cell and
by a separate calculation in the cyclotomic field.

## Consequence for local tests

Let p be an odd prime different from l, with p ≡ ±j modulo l in the above
range. For each prime v of H above p put

    bᵥ = Tr(kᵥ/Fₚ)(W · F(x)^(1/p)),

where the root is the inverse Frobenius in the finite residue field kᵥ.
Since v is unramified, the reduction of the field trace is the sum
of the residue-field traces. Raising the argument to p preserves each
residue trace and replaces W by xⱼ(xⱼ−2). Hence ∑ᵥ bᵥ = l Sⱼ modulo p.
In particular at least one bᵥ is nonzero whenever p does not divide Sⱼ.

* For every odd prime p < l/2 other than 5, at least one place works.
  Here j=p, so 4Sⱼ is congruent to 5 or −5. If p=5<l/2 the sum vanishes.
* Every odd prime p > (l+1)(l+5)/2 works at some place. The remaining
  exceptions to the **sum** test can be found by factoring the finite
  table and retaining prime divisors p ≡ ±j modulo l.
* For l=13, Sⱼ runs through −7,117,32,−4,−15,81. Thus every odd prime
  other than 5 and 13 gives a nonzero local trace somewhere. At p=71
  the value is 13·81 ≡ 59. For l=7 all odd primes other than 7 pass
  the sum test, and for l=11 only 5 is exceptional among odd p ≠ 11.

A vanishing sum at a split prime may still have nonzero summands.
The result supplies a necessary ingredient in a descent. The original
degree-13 calculation is in [the inert trace note](InertTrace13.txt).
