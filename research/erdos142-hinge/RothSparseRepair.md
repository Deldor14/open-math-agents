# Keeping the full asymptotic Roth number under a long-progression hitting constraint

Write [N]={0,…,N−1}. Let R=r_k(N) be the maximum size of a k-progression-free subset, and R_hit(N,k,L) the maximum with the additional requirement of meeting every L-term progression of positive integer step. In the following statement k≥3 may depend on N.

**Full retention.** If R log(2+N/R)=o(L) and L≤N, then R_hit(N,k,L)=(1−o(1))R. More precisely, a supplied k-free set S can retain 1−o(1) of its weight on its actual sites. This strengthens the earlier half-retention conclusion in the regime of sufficiently long windows. [Earlier result for shorter progressions](RothHalfPatches.md)

**Finite estimate.** Suppose 2≤L≤N, Q=⌈N/L⌉, p=12 log(16Q)/L and p≤1/(2√N). Given S⊆[N] k-free of size M, there is a distribution of k-free sets A hitting length L, with
$$
\Pr(x\notin A)\le 6Mp+4Np^2\quad(x\in S).
$$
In particular every nonnegative weighting admits an A retaining at least a fraction 1−6Mp−4Np² of its weight. To apply this to the extremal R use R≥r₃(N)≥N exp(−4√log N), so R≫√N. The hypothesis on L implies L≥R eventually, pR→0 and Np²→0. The same argument gives the loss bound in terms of the actual M when S is sparse. [Behrend lower estimate in mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Additive/AP/Three/Behrend.html)

## A sparse 3-free blocker with controlled point probabilities

Give each 3-free set B⊆[N] probability proportional to z^|B|, with z=p/(1−p). Equivalently this is independent Bernoulli sampling with parameter p conditioned on 3-freeness. Given every site's status except v, the probability that v is occupied is p when inserting it is allowed, and zero otherwise. Thus even after conditioning on statuses of any subset of other vertices, the chance of occupation is at most p. A prescribed pair has joint probability at most p². These bounds continue to hold under conditioning any specified set of sites to be absent.

At most 2N triples contain a fixed v: at most N choices use v as middle term and at most N as an endpoint in each direction combined (the latter follows by summing the available half lengths). Therefore the probability that v is blocked by an occupied pair is ≤2Np² even after conditioning other sites to be absent. For a still unexposed v its chance of occupation under such conditioning is at least p(1−2Np²)≥p/2. Multiplying the successive probabilities of absence bounds the chance of missing any fixed h sites by exp(−ph/2).

Take h=⌊L/2⌋≥L/3. For every admissible step q≤(N−1)/(L−1)≤2Q, divide each of its residue chains into consecutive disjoint h-site blocks, discarding the final incomplete block. Any L-term progression contains a full aligned block. There are at most N/h≤3Q blocks per step, hence at most 6Q² altogether. The probability any is missed is ≤6Q² exp(−pL/6)<1/2. Condition B on hitting all of them. A single-site probability and a specified pair probability are now bounded by 2p and 2p² respectively.

## Repair on the original input sites

From S discard x if a distinct site b in B and a third distinct y in S∪B form a triple with x in any role. For each y∈S different from x, there are at most three possibilities for b. The remaining risk comes from two sites in B, with at most 2N pairs for fixed x. These two union bounds give the stated probability of deletion. Adjoin B to the retained sites. Any k-term progression involving a site outside B and a site in B has a consecutive mixed triple and was prevented by the deletion rule. A progression entirely in one group is excluded by the relevant input's freeness. The final set hits every L-window and contains the retained sites. Averaging proves the weighted statement.

## Simultaneously specifying sites and retaining the actual extremal size

For k=3 there is a further conclusion. Under the full-retention hypothesis on L, prescribe a 3-free S₀ of f=o(N/R) positive sites and a disjoint set T of o(L) negative sites. There exists a 3-free set of (1−o(1))R sites that satisfies both prescriptions and hits every L-window.

First exclude T, S₀ and all completions of pairs of S₀ from the candidate ground set. These exclusions cost at most |T|+f+3 choose(f,2)=o(L), using N/R=N^o(1) and L≥R. Forbid every triple of candidates, and forbid each candidate pair forming a triple with some point of S₀. Sample independent subsets in this finite family as above, now with p=24 log(16Q)/L. The probability that a candidate is blocked given earlier absences is at most 3fp+2Np²=o(1), by the same one- and two-site upper marginals. Each h-block contains ≥L/4 candidates for large N. The union bound gives simultaneous hitting with probability >1/2. The unconditional expected size is ≤Np, so some hitting sample has size ≤2Np. Its union F with S₀ is free and |F|≤f+O(Q log(16Q))=o(N/R). Apply the prescribed-site estimate (2) of the earlier note with F and T. It gives a near-extremal set containing F and avoiding T. Hitting persists under taking supersets. [Prescribed-site estimate](RothExtensions.md)

[The Lean file](RothSparseRepair.lean) checks the exact occupation identity for a hereditary family, the single- and two-site upper marginal estimates and the lower marginal from forbidden pairs, aligned-window containment and progression-freeness after repair for every k≥3. [The companion theorem](RothPinnedWindows.md) treats exact retention of prescribed points in much shorter windows.
