# Half of a prescribed progression-free set can be retained with all long progressions hit

Let [N] denote the integers from 0 through N−1. A set hits length L if it meets every L-term arithmetic progression in [N] of positive integer step. A **protected pair** consists of disjoint P,B ⊆ [N] such that B hits length L, B is 3-free, and for every k≥3, adjoining B to any k-free subset of P preserves k-freeness. Here k-free means containing no nonconstant k-term arithmetic progression.

**Theorem.** For each fixed 0<δ<1/2 and every sufficiently large N, there is a probability distribution of protected pairs with

$$
L\le \exp(C_\delta(\log N)^{5/6}),\qquad
\Pr(x\in P)\ge 1/2-\delta \quad\text{for every }x\in[N].
$$

Thus for every k-free S and any nonnegative weights on its sites, some k-free set meeting all length-L progressions retains at least 1/2−δ of the original weight. The same distribution works for every k, S, and choice of weights. The construction can also be applied to a single extremal S with unit weights.

Write U(N,L) for the maximum possible size of the first member of a protected pair, allowing zero if no pair exists. At the explicit length

$$
L_*(N)=\left\lceil\exp((\log N)^{5/6}\log\log N)\right\rceil
$$

one has **U(N,L_*(N)) = (1/2+o(1)) N**. The matching upper bound concerns the region on which arbitrary free data can be prescribed. How much of a particular extremal set can be retained may depend on that set.

The estimate concerns a restricted Ramsey problem associated with Erdős 142. It gives an additive log 2 + o(1) upper bound for the increase in the logarithmic density deficit caused by the all-step hitting constraint at length L_*. The actual asymptotic size of the unrestricted extremal set remains unknown.

## A region stable under the midpoint constraints

On the d-dimensional torus write |b|₁=∑ᵢ ||bᵢ||, where ||·|| is circle distance to zero. We first construct a region P₀ of Haar measure ≥1/2−δ and an auxiliary region U={b : |b|₁ ≤ ρ√d}, for some ρ>0 depending only on δ. They are disjoint, and any torus midpoint triple in their union that uses both regions is impossible.

For a positive integer m let
$$
f(x)=\sum_{j=0}^{m-1}(-1)^j\sin(2\pi 2^j x),\quad
F(x)=\sum_{i=1}^d f(x_i),\quad K=2\pi(2^m-1).
$$
The function is odd, and translating F by b changes its value everywhere by at most K|b|₁. Put D=Kρ√d and
$$
P_0=\{x:F(x)>3D,\ F(2x)<-3D\}.
$$
For b in U one has |F(b)|≤D. For p,p′ in P₀ and b,b′ in U, the four mixed midpoint patterns are excluded by the following inequalities.

* If p+p′=2b, oddness and two allowed translations give |F(p′)+F(p)|≤2D.
* If p+b=2p′, then |F(2p′)−F(p)|≤D.
* If b+b′=2p, then |F(2p)|≤2D.
* If b+p=2b′, then |F(p)|≤3D.

Each conclusion contradicts a strict defining inequality. This argument also works with a general odd function on an abelian group.

For uniform independent torus coordinates, f has mean zero and variance m/2 by orthogonality. Also f(x)+f(2x)=sin(2πx)+(−1)^(m−1) sin(2π 2^m x), of mean zero and variance 1. Normalize by σ=√(dm/2). For fixed m, F/σ tends in distribution to a standard normal as d→∞ by the classical central limit theorem, and the variance of (F(x)+F(2x))/σ is 2/m.

Choose u>0 so that Pr(Z>2u)>1/2−δ/3 for a standard normal Z. Choose a fixed m so large that 2/(m u²)<δ/3. Then take ρ>0 small enough that 3Kρ ≤ u√(m/2), and ρ≤1/10. For all sufficiently large d the event F/σ>2u has probability >1/2−2δ/3. By Chebyshev the probability that |F(x)+F(2x)|/σ≥u is <δ/3. On the resulting intersection F>3D and F(2x)<−3D, proving the mass bound. The alternating signs make the values at x and 2x nearly opposite on the normalized scale.

Ruzsa's construction of a dense set with no long progression in its sumset is a precedent for using density close to one half and high-dimensional approximation. Here the second inequality on F additionally controls a prescribed point appearing in the middle of a triple, and the auxiliary sites must themselves be 3-free. [I. Z. Ruzsa, *Arithmetic progressions in sumsets*, Acta Arithmetica 60 (1991)](https://doi.org/10.4064/aa-60-2-191-202)

## Uniform visits to U containing a full subprogression

The following argument applies to all starting phases, not just integer multiples of the rotation. Fix ρ>0 as above, an integer ℓ≥2, and d sufficiently large depending only on ρ. Put
$$
w=\rho/(4\sqrt d),\quad s=\lfloor\rho\sqrt d\rfloor,\quad
K_0=\lceil16d\,w^{-d-1}\rceil,\quad
E=\{-K_0,\ldots,K_0\}^d,\quad
\eta=(4|E|)^{-1}(4N)^{-1/s}.
$$
In particular s≥1. Choose θ Haar-uniform on the d-torus. For any fixed positive q≤N and any s rationally independent vectors of E, their evaluations on qθ are jointly Haar on the s-torus, since the defining integer matrix has full row rank. The probability all evaluations have norm ≤η is (2η)^s. A union bound over q and ordered tuples gives N(2η|E|)^s = 2^(−s)/4 < 1. Fix a successful θ.

For each q the rational span of the nearly resonant vectors in E has dimension t<s. In a basis matrix for that span choose t pivot columns. Deleting the corresponding coordinates leaves a set J on which **no nonzero frequency supported in J belonging to E can be nearly resonant**. Indeed a vector of the span with zero pivot coordinates vanishes. This argument controls only the number of discarded coordinates; their phases are arbitrary.

On the retained coordinates use the product of the circle functions ψ(x)=(1−||x||/w)_+. Their one-dimensional Fourier coefficients are w at zero and sin²(πhw)/(π² h²w) at nonzero integer h. They are nonnegative and sum to one by absolute convergence and evaluation at zero. The total coefficient mass with |h|>K₀ is ≤2/(wK₀). Thus the product has constant coefficient w^|J|≥w^d and total mass outside its frequency box at most 2d/(wK₀)≤w^d/8.

Set M=⌈w^(−d)/η⌉. Given any starting phase γ, average the product at γ+(M+j)qθ with weights (M−|j|)_+/M² on the integers j. The transform of the weights is the squared absolute value of the length-M normalized geometric sum. Its absolute value is ≤1 and at a frequency of circle norm >η is ≤1/(4M²η²). All nonzero frequencies in the retained box enjoy this bound by the pivot argument. The average is at least w^d−w^d/8−1/(4M²η²)>0. So at an index b between 0 and 2M every retained coordinate has norm <w.

Partition the retained torus into cubes of side 1/⌈ℓ/w⌉. Pigeonholing consecutive multiples of qθ yields an integer 1≤h≤⌈ℓ/w⌉^d with ||h qθᵢ||≤w/ℓ on each retained coordinate. For 0≤j<ℓ the orbit at b+jh has retained coordinate norms ≤2w. Each of the t discarded coordinates contributes at most 1/2 to the total. Hence
$$
|\gamma+(b+jh)q\theta|_1 \le 2dw+t/2 \le \rho\sqrt d .
$$
All these points are in U. The largest index is less than L=2M+1+(ℓ−1)⌈ℓ/w⌉^d. Taking logarithms and using log |E|=O_ρ(d² log d), s≫_ρ√d, gives
$$
\log L\ll_\rho d^2\log d+\frac{\log N}{\sqrt d}+d\log(2\ell).
$$

## Placing the prescribed and auxiliary sites

Haitao Cao's lower bound for w(3,ℓ) gives a 3-free H⊆[N] meeting every ℓ-term progression with ℓ≤exp(C√log N) for all large N. Choose d=⌈(log N)^(1/3)⌉. The preceding estimate gives log L ≤ C_δ(log N)^(5/6), since d² log d=o((log N)^(5/6)). [Cao, Theorem 1.1](https://arxiv.org/html/2609.31798v1)

For a Haar-uniform phase β define P={x∈[N] : β+xθ∈P₀} and B={x∈H : β+xθ∈U}. Each site's probability of lying in P equals the Haar measure of P₀. Every L-term progression contains an ℓ-term subprogression in the inverse image of U by the orbit lemma, applied to its first phase and step. This subprogression has positive step and is met by H. Thus B hits all the required progressions for **every** β.

The affine map preserves midpoint identities. Any k-term arithmetic progression in T∪B with k≥3 would therefore keep the same region label across its overlapping triples. This is impossible if T⊆P is k-free, since B is 3-free. For a given weighted S average the sum of its weights on P and use T=S∩P.

The same auxiliary set works for the two disjoint patches obtained from F and −F, since U is unchanged. Every site has probability at least 1−2δ of lying in their union. Thus two extensions sharing one blocker can together retain at least 1−2δ of the weight of any prescribed free set.

There is a counting consequence at the same length. Write I for all k-free subsets of [N] and J for the L-hitting members. For a uniformly random S in I, order its site indicators X₁,…,X_N. At a fixed patch P, the entropy of the restriction S∩P is at least the sum over x∈P of H(X_x | all preceding indicators), by the chain rule and monotonicity under conditioning. Each such restriction embeds injectively in J by adjoining B, so this entropy is at most log |J|. Averaging over the independent phase and applying the chain rule again gives log |J| ≥ (1/2−δ) log |I|.

For the upper bound on U(N,L), take a hit b in the length-L interval starting at ⌊(N−L)/2⌋, with L≤N. The distances |x−b|, x∈P, are distinct positive integers. An equal distance from two distinct sites yields a 3-free two-point input whose union with B contains a triple. Therefore |P|≤max(b,N−1−b) and 2|P|≤N+L. Conversely, the theorem and the expected size of P give |P|≥(1/2−δ)N for some phase. For fixed δ, L_*(N) eventually exceeds the constructed L because log log N→∞. Sending δ to zero and using L_*(N)=o(N) gives the claimed asymptotic.

For completeness, if R_hit denotes the largest size of a k-free L_*(N)-hitting set, the weighted theorem gives R_hit/r_k(N)≥1/2−o(1), uniformly in k≥3. If no particular input is specified, R_hit≤r_k(N) by definition. This yields the stated comparison of logarithmic deficits.

## Verification scope

[The Lean file](RothHalfPatches.lean) proves the four mixed-triple contradictions on arbitrary abelian groups and the sharp upper constant directly from the protection hypothesis on two-point inputs. The probability estimates, Fourier argument and use of Cao's theorem are the written part of this proof. [The preceding note](RothRamseyPatches.md) gives the underlying gluing theorems and a complete finite instance.

[The exact integer verifier](check_roth_half_patches.py) uses an odd triangular wave on two finite cyclic groups, checks all four types of mixed triple for each tested auxiliary shift, and enumerates all disjoint protected pairs on intervals of up to nine sites. The larger cyclic test has 25,695 protected sites among 65,537.
