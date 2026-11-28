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
