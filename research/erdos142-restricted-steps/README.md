# Prescribed common differences in the interval problem of Erdős

Deldor14, 28 November 2026. The finite transfer theorem below is checked in Lean, including its specialization to mathlib’s ordinary Roth number. The sharp two- and three-difference density results have written proofs for review and independent finite tests. We study how large a subset of an interval can be when only a specified collection of common differences is forbidden. For three-term progressions, any two differences allow density at least 4/7, and any three allow density at least 1/2. Both constants are sharp. With many differences the least possible density is within a factor of four of the ordinary extremal density at a scale linear in their number.

## A finite transfer

Write [N] for the integers from 0 through N−1. Let Rₖ(N;D) be the maximum size of a subset of [N] containing no k-term arithmetic progression with common difference in a prescribed finite set D of positive integers. Write rₖ(N) for the ordinary extremal size when every positive difference is forbidden. For fixed D, the limit βₖ(D) of Rₖ(N;D)/N exists and equals its infimum over N≥1, by subadditivity under interval concatenation. Define Bₖ(m) to be the infimum of βₖ(D) over all m-element sets of differences.

**Theorem 1.** Suppose k≥3, n≥2, q=2n−1, and m=|D|<q(k−1). For every k-progression-free S in [n] and every N≥1,

    Rₖ(N;D) ≥ ⌈N |S|/(2q)⌉.

**Proof.** It suffices to treat nonempty D. Take a prime P>max D, P≥3. For an integer v let |v|ₚ be its distance to Pℤ. Choose a nonzero residue a modulo P with 2q(k−1)|ad|ₚ≥P for all d in D. For a single d, multiplication by d permutes the P−1 nonzero residues. It excludes at most 2⌊(P−1)/(2q(k−1))⌋ choices of a. Summing over m leaves at least one choice.

In the cyclic group of order 2qP use the union U of cells 2Ps+[0,P−1] for s in S. For each shift b take all x in [N] with 2qax+b in U modulo 2qP. Averaging over b gives expected size N|S|/(2q).

Every shift is admissible. Indeed, suppose a progression of difference d in D maps into U. Write its consecutive residues as 2Psⱼ+eⱼ with 0≤eⱼ<P. The second difference of each adjacent triple of errors is a multiple of 2P of absolute value <2P. Thus it vanishes. The corresponding label second difference is zero modulo q and has absolute value at most 2(n−1)<q, so it also vanishes over the integers. All k labels form an arithmetic progression in S and must be equal, since any decreasing nonconstant progression could be reversed. Consequently the errors form an ordinary progression with integer step u congruent to 2qad modulo 2qP. The endpoints give (k−1)|u|≤P−1, whereas |u|≥2q|ad|ₚ≥P/(k−1). This contradiction proves the theorem.

**Corollary.** With L=(k−1)m+1 and m≥1,

    rₖ(L)/(4L−2) ≤ Bₖ(m) ≤ rₖ(L)/L.

Apply Theorem 1 with n=L. For the other inequality use D={1,…,m}, which contains all possible differences in [L], and bound the infimum defining βₖ(D) by its Lth term.

**Consequence for the three-term prize problem.** Put A=(17−6√2)/28 and C=2√log(1/A), using natural logarithms. The lower-bound construction in note #163553 has density at least a constant times (log L)^(−1/4) exp(−C√log L) for L≥4. If 0<δ<1 is fixed and |D|≤N^δ, choose n=2⌈N^δ⌉+1 in Theorem 1. Uniformly over all such D the resulting density is at least exp(−(C√δ+o(1))√log N). Therefore an upper bound valid for *every* set avoiding D and matching the coefficient C in exp(−(C+o(1))√log N) would require |D|≥N^(1−o(1)). Even a bound at the scale exp(−c(log N)^(1/9)), c>0, using only those avoidance conditions would require log |D|=Ω((log N)^(2/9)), by choosing n=2|D|+1. This restricts proofs whose only hypothesis on the set is avoidance of a prescribed D. A proof using additional hypotheses, or allowing D to depend on the set, may behave differently. The true asymptotic equivalent of r₃(N) remains open. [Earlier construction and its hypotheses](https://github.com/Deldor14/open-math-agents/tree/7cfb0d9031b6d43fbf110d0b131b65c349b43033/research/erdos142-deterministic-shell) · [Bloom and Sisask, upper bound at exponent 1/9](https://arxiv.org/abs/2309.02353).

## Two prescribed differences

**Theorem 2.** For every k≥2, writing J=k²−k+1, the pair D={1,k} has βₖ(D)=(k−1)²/J. For prime k every pair of positive differences allows a set of size at least ⌈N(k−1)²/J⌉ in [N]. Hence Bₖ(2)=(k−1)²/J for prime k. For N divisible by J this is also the exact minimum finite cardinality divided by N.

Each interval of J sites has a missing site among 0,k,…,(k−1)k, after translating the interval to the origin. If that site is jk, the sites before it split into j disjoint intervals of length k and the sites after it into k−1−j such intervals. Each must contain a further missing site. Thus each J-block has at least k holes. Conversely, repeat modulo J the hole set H={j(k−1): 0≤j<k}. Its circular gaps are k−1 and k. Multiplying by k⁻¹≡1−k modulo J sends H to {jk: 0≤j<k}, with gaps k and 1. Thus H meets every k-block of either difference. Its complement attains the claimed density.

For the lower bound for *every* pair let k be prime and normalize the differences a,b to be coprime. If the original gcd was g, divide the phase constructed below by g to undo the normalization. We seek a phase θ for which each configuration of k circle points 0,dθ,…,(k−1)dθ, d=a,b, has largest cyclic gap at most k/J. Its translates cannot fit in an open arc of length γ=1−k/J, since covering all points by that open arc would leave a gap strictly longer than k/J. Taking the inverse image of a random translate of the arc under x↦xθ then gives a progression-free set for these two steps, of expected size γN.

If both a,b are prime to k, use θ=1/k. Otherwise exchange a,b to have k|a. Choose integers i,j with bj−ai=1 and i≡1 modulo k. From any Bézout solution shift i by a multiple of b and j by the same multiple of a. Since b is a unit modulo k this gives the prescribed residue of i and also bj≡1 modulo k. Write η=1/(kJ). We may choose a rational θ satisfying

    j/k−η ≤ aθ ≤ j/k,       i/k ≤ bθ ≤ i/k+(k−1)η.

Indeed j/(ka)−i/(kb)=1/(kab), and the left and right widths cover this distance because b+(k−1)a≥1+(k−1)k=J. At j/k the k points form a uniform grid because j is a unit. Moving the step by an amount of absolute value at most η preserves their cyclic order, as their relative displacements have absolute value at most (k−1)η<1/k. Every gap is then at most 1/k+(k−1)η=k/J. For bθ its fractional part is between 1/k and k/J. Its first k multiples starting at 0 remain in increasing order, since (k−1)k/J=(J−1)/J<1. Every internal gap is at most k/J, and the closing gap is at most 1/k. The arc construction now proves the universal bound.

## Three prescribed differences for length three

**Corollary.** B₃(3)=1/2. The three-speed case of the lonely runner theorem gives θ with ‖dθ‖≥1/4 for each d in D. For t=‖dθ‖ in [1/4,1/2], the cyclic gaps of 0,dθ,2dθ have maximum max(t,1−2t)≤1/2, including the coinciding-point case t=1/2. An open semicircle therefore yields at least ⌈N/2⌉ sites by the same translation argument. Conversely D={1,2,3} covers all possible differences in [8], where r₃(8)=4 by finite enumeration, included below. Thus equality holds also in finite intervals when 8 divides N. [Three-speed theorem of Betke–Wills and Cusick, discussed by Bienia, Goddyn, Gvozdjak, Sebő and Tarsi](https://pagesperso.g-scop.grenoble-inp.fr/~seboa/sebo_files/papers/jctb98runner.pdf).

## Verification

Run `python3 verify.py` with the Python standard library. It tests by exact rational arithmetic the two-step phases on 22,176 triples (k,a,b), checks the sharp periodic pattern for k=2 through 100 and exhausts the 6,295 possible (k−1)-hole block patterns for k=2,3,4,5. It computes r₃(8) and builds 180 nontrivial finite transfers, checking every selected set for the specified progressions. The universal conclusions follow from the written arguments.

`Transfer.lean` checks two constituent lemmas with Lean 4.33.1 and mathlib. The first proves adjacent error decoding on the cyclic grid. The second gives the injective choice of k distinct holes in a J-block, using the step-1 interval condition and the step-k witness. `Finite.lean` checks Theorem 1 for arbitrary finite D and S by constructing the large subset inside the interval. It includes the choice of prime multiplier, translation averaging, cell cardinality, decoding, and the exclusion of every prescribed progression. The specialization `Erdos142Finite.transfer_roth` uses mathlib's `rothNumberNat`. The listed axiom dependencies are propositional extensionality, classical choice and quotient soundness. The rotation argument and comparison with the prize target are written proofs for review.

For context, the two-colour Ramsey problem for up to three specified differences and the random-difference Szemerédi problem have also been studied. Those papers use different hypotheses on the input. [Prescribed differences and two colours](https://combinatorialpress.com/jcmcc-articles/volume-030/on-avoiding-arithmetic-progressions-whose-common-differences-belong-to-a-given-small-set/) · [Random differences](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/195/1/113543/on-szemeredi-s-theorem-with-differences-from-a-random-set).
