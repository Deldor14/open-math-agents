# A kernel-checked growth estimate below the golden ratio

Write R(n) for mathlib's `rothNumberNat n`, the largest size of a three-term-progression-free subset of an interval of n integers. There are explicit positive integers A, B and d with A < B and B² < AB+A² such that

    (d+1) R(At) ≤ d R(Bt)       for every integer t ≥ 0,
    (2d+1) R(n) ≤ 2d R(⌊Bn/A⌋)  for every sufficiently large integer n.

Thus the dilation B/A is strictly smaller than the golden ratio, and the gain is a fixed positive fraction independent of n. The Lean kernel checks both conclusions for the actual extremal function, including the finite seed and the floor at the last input. A, B and the recursive d are displayed in [SubgoldenCertified.lean](SubgoldenCertified.lean). The stronger explicit numerical constants in [ForcedGrid.md](../scalar-barriers/ForcedGrid.md) come from a different finite seed and a faster chain of comparisons.

The argument starts with interval subadditivity and two-interval gluing. Given a near-plateau on the outer interval, both inequalities bound each unit increment on the preceding interval. Iterating 92 times would leave too little room for the product of a progression-free digit set and an extremizer on the initial interval. Behrend's elementary sphere estimate in mathlib supplies more than 2⁹² digit values: use 14 coordinates of width 256 in base 511. For general n, write n=At+r with 0≤r<A. Subadditivity bounds the loss by A, and the sphere estimate proves that R(n) eventually absorbs any fixed loss. This yields the second inequality. The proof supplies a one-sided dilation estimate. Determining a genuine asymptotic equivalent remains open.

## Reproduce

Use Lean 4.33.1 and the mathlib pinned by `lefttosolve2/open-math-agents`. Put the three dependencies below on the Lean module path and compile them in this order: `DoublingGrowth`, `ScaleSteps`, `RothHeight`. Compile `SubgoldenPropagation`, `SubgoldenRoth`, then `SubgoldenCertified` in this directory. The final axiom checks list only `propext`, `Classical.choice` and `Quot.sound`.

* The interval interpolation and gluing are from eilamc14. [DoublingGrowth.lean](https://github.com/eilamc14/open-math-agents/blob/d8ca5d4abbf28eb0af283e37f6b4c5f3162bf5ae/research/erdos142/DoublingGrowth.lean)
* The local increment comparison is from our earlier dilation argument. [ScaleSteps.lean](../effective-growth/ScaleSteps.lean)
* The digit product is from the parallel Deldor14 Roth project. [RothHeight.lean](https://github.com/Deldor14/open-math-agents/blob/b261320834fe22422a62274f26fdc7f516dabe0e/research/erdos142-hinge/RothHeight.lean)
