# A finite doubling inequality for Erdős #142

For every k ≥ 4 and every natural N, the maximum r_k on the one-based interval satisfies

    r_k(2N) ≥ r_k(N) + r_k(ceil(N/2)).
    2 r_k(2N) ≥ 3 r_k(N).

This includes k = 4, extending the range k ≥ 5 recorded in Left to Solve note 103490. For k = 4 and N = 2 the factor 3/2 is attained. These finite inequalities leave the full asymptotic equivalent open.

Take an extremizer A in [1,N] and an extremizer B in [1,ceil(N/2)]. Place the disjoint sets 2A and 4B−3 in [1,2N]. Residue 3 modulo 4 is absent, so an arithmetic progression of length at least four cannot have odd difference. A progression of even difference is confined to one parity. In the even layer it pulls back to A. In the odd layer its difference must be divisible by four, since every member is 1 modulo 4, so it pulls back to B. For the second inequality, splitting [1,N] into two intervals gives r_k(N) ≤ 2r_k(ceil(N/2)).

## Files

- ParitySplit.lean proves an exact odd/even decomposition of avoidance for every even progression length, using Lean core.
- UpstreamParity.lean identifies the run formulation with Set.IsAPOfLengthFree for every length greater than one.
- Doubling.lean proves both inequalities for Set.IsAPOfLengthFree.maxCard itself. The constructive proof in this file also covers odd k ≥ 5.

Verified with Lean 4.33.1 and formal-conjectures commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53 (FormalConjecturesForMathlib.Combinatorics.AP.Basic). The three files use no placeholders. The axiom audit on the two final theorems lists propext, Classical.choice and Quot.sound.

To reproduce, build the pinned upstream AP.Basic module first. From the directory containing these three files, with that upstream module and its dependencies on LEAN_PATH and the same directory also on LEAN_PATH, run:

    lean -DwarningAsError=true -o ParitySplit.olean ParitySplit.lean
    lean -DwarningAsError=true -o UpstreamParity.olean UpstreamParity.lean
    lean -DwarningAsError=true -o Doubling.olean Doubling.lean

## Prime-power dilation

For every prime p, integer h ≥ 0, progression length k ≥ p^(h+1), and N ≥ 0, the maximum satisfies

    r_k(pN) ≥ p r_k(N) − floor(r_k(N)/p^h).

For example, the guarantees at (p,k) = (2,8), (3,9), (5,5) are 7/4, 8/3, and 4 times r_k(N), respectively, with upward integer rounding. At k = p^(h+1) and N = p^h the formula gives equality. These examples establish sharpness of the uniform factor across the stated range, without asserting the optimal factor for each larger fixed k.

Expand each point of an extremal set into a full block of p consecutive integers. Delete the least occupied residue class modulo p^(h+1). Every progression whose step is not divisible by p visits the deleted class among its first p^(h+1) terms. A progression whose step is divisible by p projects back to a forbidden progression in the original set. The candidate uses at least the number of points in the displayed formula.

Additional file PrimePower.lean proves prime_power_dilation, initial_values and prime_power_sharp on the same upstream definition. With the preceding three files built and Mathlib.Combinatorics.Pigeonhole available, run

    lean -DwarningAsError=true -o PrimePower.olean PrimePower.lean

The dilation and sharpness theorems both report only propext, Classical.choice and Quot.sound.
