# Positive solutions of u² + d⁵ = 2ᵏ

For positive integers u and d and any nonnegative integer k, the solutions are precisely

    (u, d, k) = (2^(5t), 2^(2t), 10t + 1),   t ≥ 0.

This is a consequence of Jamie Mulholland's published point classification in his PhD thesis, Theorem 5.1 and Table 5.1, printed pages 177–178. [Original thesis](https://www.sfu.ca/~jtmulhol/papers/Mulholland-phd-thesis.pdf#page=185)

Write k = 10t + j with 0 ≤ j < 10 and set q = 2ᵗ. Then X = −d/q² and Y = u/q⁵ are rational, X < 0 < Y and Y² = X⁵ + 2ʲ. In the positive-sign, beta-zero part of Mulholland's table, the only finite point with these signs is (−1,1) at j = 1. The exceptional curve excluded in Theorem 5.1 has negative sign and beta = 9. Substitution gives the displayed triple. Its converse follows by direct expansion.

In particular, if d is odd, then t = 0 and d = 1. This proves the mathematical statement of the Left to Solve step for every exponent, including the range k > 10001 left in note 108372. [Exact step](https://lefttosolve.com/p/BealConjecture.beal_conjecture.R2.H3.R1.H1.R1.H2)

The new file TableReduction.lean proves the classification and its odd-base corollary in Lean 4.33.1 with Mathlib, with the indicated consequence of Mulholland's table passed as the explicit hypothesis TableInput. The rational-point classification itself is supplied by the cited thesis.
