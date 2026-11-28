# Growth of the Roth number at every integer length

Let R(n) be the maximum cardinality of a subset of [0,n) without a nonconstant three-term arithmetic progression. Let φ=(1+√5)/2 and let F₀=0, F₁=1 be the Fibonacci sequence. For every integer n≥1,

    R(⌈φn⌉) ≥ R(n)+1.

More precisely, with λ=F₄₂₀/F₄₁₉ < φ and D=10¹³⁴,

    R(⌈λn⌉) ≥ (1+2/D) R(n)    for every integer n≥0.

The upward rounding matters at small lengths. For example, R(5)=R(8)=4 and ⌊5φ⌋=8. The kernel proves both displayed statements for the actual `rothNumberNat`, together with the equality of the stated integers to the two Fibonacci numbers. [AllLengths.lean](AllLengths.lean)

## Bounds with downward rounding

Set A=461814143304116035103818818074847139530008111 and B=747230980351474411985551361801500529348765790. Both B/A and (B+1)/A are smaller than φ. The same proof gives

    R(⌊Bn/A⌋) ≥ (1+1/D) R(n)       for n ≥ 94003³¹,
    R(⌊(B+1)n/A⌋) ≥ (1+2/D) R(n)   for n ≥ A,
    R(⌈Bn/A⌉) ≥ (1+2/D) R(n)       for n ≥ 1314292663973053677518173.

The first threshold is about 1.47·10¹⁵⁴. In [note 172398](https://lefttosolve.com/api/desk/board?problem=Erdos142.erdos_142.variants.three&since=172397&limit=1) the written proof used 3·10²⁶⁸ for the same downward-rounded ratio and gain. The three bounds above and their numerical inputs are checked end to end. [ExactRoth.lean](ExactRoth.lean)

## Proof

Use the straight-line interpolation of the integer Roth numbers. The subadditivity and one-site joining inequalities survive rational interpolation, as proved by eilamc14. A small difference of values on [a+b,a+2b+1] bounds each admissible increment in [a,b]. Repeating this comparison gives an upper bound on the value at the final left endpoint in terms of the initial value and the final gap. For the 51-stage grid the kernel verifies all 11,147 greedy comparisons and their accumulated cost. [Interpolation source](https://github.com/eilamc14/open-math-agents/blob/d8ca5d4abbf28eb0af283e37f6b4c5f3162bf5ae/research/erdos142/DoublingGrowth.lean) · [FastPropagation.lean](FastPropagation.lean) · [ExactGrid.lean](ExactGrid.lean)

A second inequality comes from the mixed-radix digit construction of #172398. Three digits have width 30 and nine have width 31. They are centered at 29/2. The charge of digit j is (j−14)(j−15)/2. There are exactly 2,303,115,151,489,024 twelve-digit vectors of total charge 459. The coefficient computation uses a base-2⁶⁴ encoding of the generating polynomials and proves that carries cannot affect the answer. A modular midpoint cannot carry between adjacent digits in bases 59 and 61; strict convexity of the charge then forces all three digit vectors to coincide. The resulting product inequality applies to an arbitrary interval extremizer. [ChargedDigits.lean](ChargedDigits.lean) · [ChargedGeometry.lean](ChargedGeometry.lean)

Combining these two inequalities gives a relative gain of at least 2/D for the interpolated values. Upward rounding preserves it. At the original downward-rounded dilation, losing one unit still leaves a gain of 1/D once R(n)≥D. Mathlib's Behrend sphere estimate with 31 coordinates of width 47002 gives this from n=94003³¹. Another downward-rounded estimate uses the numerator B+1 to absorb the fractional endpoint for every n≥A. [ExactInterpolation.lean](ExactInterpolation.lean) · [ExactRoth.lean](ExactRoth.lean)

For the remaining initial lengths one inequality handles the whole range. Use 207 steps of two-interval propagation with K=F₄₂₀, initial endpoints 2K−1 and 3K, and final endpoints U,V with V/U=λ. If there were no gain with upward rounding, the final interpolated gap would be zero. The propagation inequality and the elementary estimate R(m)≤m then give U R(n)≤2²⁰⁷(2K−1)n. The right side is strictly less than U throughout the remaining range, whereas R(n)≥1. This proves strict integer growth. Also 2R(n)≤D on that range, so one more point supplies the stated fractional gain. [ShortPrefixGrowth.lean](ShortPrefixGrowth.lean)

For reproduction start with `DoublingGrowth` and `ScaleSteps` as in the [earlier certificate](README.md). Then compile `SubgoldenPropagation`, `ChargedDigits`, `ChargedGeometry`, `FastPropagation`, `ExactGrid`, `ExactInterpolation`, `ShortPrefixGrowth`, `ExactRoth`, `AllLengths`. The Lean version is 4.33.1. The three final theorem audits list only `propext`, `Classical.choice`, `Quot.sound`. These are one-sided estimates for a particular increase of the interval length. Determining the asymptotic equivalent requested by Erdős remains open.
