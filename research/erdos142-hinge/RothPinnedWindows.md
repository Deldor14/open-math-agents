# How many points can be prescribed in a progression-free set meeting every long progression?

Write [N]={0,…,N−1}. An L-window is an L-term arithmetic progression of positive integer step in [N]. Define s(N,L) to be the largest integer s≤N such that every 3-free S⊆[N] with at most s sites is contained in a 3-free set meeting every L-window. If the empty prescription cannot be extended, set s(N,L)=−1.

**Square-root order for the number of prescribed sites.** For each fixed 0<c<√(2/3) there is C such that, for all sufficiently large N and
$$
\exp(C\sqrt{\log N})\le L,\qquad 8L+1\le N,
$$
one has
$$
\lfloor c\sqrt L\rfloor\le s(N,L)<4\sqrt L.
$$
The lower bound still holds for L≤N without the assumption 8L+1≤N. In the lower bound one may start with any k-free set for k≥3, asking that the extension remain k-free. The upper bound is for k=3. The matching order persists when L is smaller than every fixed power of N, with an appropriate constant in its lower threshold.

The term prescribed means that all original sites must be present in the extension. The minimum size of a hitting set with unprescribed sites is a separate extremal problem studied by Korsky. Numeral-system constructions for 3-AP saturation in other ambient groups also appear in the literature. The result below concerns the worst prescribed set and requires that the extension meet every common difference simultaneously. [Korsky, *Hitting Arithmetic Progressions at the Square-Root Scale*](https://arxiv.org/abs/2606.01780) · [Complete 3-term AP-free sets of small size](https://real.mtak.hu/225483/)

The proof allows prescribed sites of both colors. If disjoint sets S,T are required to be present and absent, respectively, S is k-free, and
$$
|T|+|S|+3\binom{|S|}{2}\le(1-\delta)L
$$
for fixed δ>0, the same extension exists for L≥exp(C_δ√log N). Thus the known quasipolynomial lower bound for the asymmetric van der Waerden number persists under these initial color assignments. A prescribed absent block of L consecutive sites by itself already prevents extension.

## Aligned blocks and intersections between common differences

For the one-color prescription fix a small constant η>0 with 1−η>3c²/2. For a two-color prescription take 0<η<δ. Put d=⌊η L⌋≥1 and h=L−d. For each admissible step q partition [N] into its residue chains and test every full h-site block whose starting index in the chain is a multiple of d. Each L-window contains a test block, by moving its start forward by at most d−1 sites. For fixed q a site belongs to ≤⌈h/d⌉ blocks. There are at most N² test blocks altogether, since its first site and step specify each one. Constants below may depend on η.

Two h-site progressions of different steps q,r intersect in at most 1+(h−1)/max(q/g,r/g) sites, where g=gcd(q,r). Distinct common sites differ by a multiple of lcm(q,r) and the shorter physical span is (h−1)min(q,r).

Let C₀⊆[N] have at most O(L) sites. Suppose ℓ≥2, ℓ²=o(L), and T=⌊h/(3ℓ)⌋. Call a test block rich if it contains at least T sites of C₀. There are **O(ℓ⁶)** rich test blocks. Here is a proof uniform in the ambient length. Let M=|C₀|. There are none if M<T. Otherwise choose an integer K ≥ 8hM/T² minimal with K≥1; thus K=O(ℓ²). Pick a maximal subfamily of rich slopes such that each pair has max(q/g,r/g)>K. Choose one rich block per selected slope and mark exactly T sites of C₀ in it. Intersections have size ≤1+h/K ≤ T²/(4M) for sufficiently large L since T²/M→∞. If at least k=⌈2M/T⌉ slopes had been selected, the union of the marked sets in the first k blocks would have size at least
$$
kT-\tbinom{k}{2}T^2/(4M) \ge kT- kT/4 > M .
$$
Here k−1<2M/T gives the middle bound. This is impossible. Each rich slope is within the specified ratio bound of a selected slope and so has ≤K² possibilities per representative (the numerator and denominator of the reduced ratio are at most K). For each resulting slope there are O(M/T) rich blocks by bounded overlap. This proves the claim. The pair-overlap inequality used here is [verified in Lean](RothRichBlocks.lean).

## Adding the prescribed sites to a two-color witness

Cao's Theorem 1.1 gives a 3-free H⊆[N] hitting every ℓ-window for an integer ℓ=⌈exp(C₀√log N)⌉ with an absolute constant C₀ large enough. Indeed w(3,ℓ)>N, so a two-color witness can be restricted to [N]. Fix this ℓ. Take C in the displayed theorem large enough that L≥ℓ¹⁶ for all large N. [Cao, Theorem 1.1](https://arxiv.org/html/2609.31798v1)

For a set V define D(V) to consist of V and every site of [N] that forms a nonconstant triple with two distinct sites of V. There are at most three possible completions for a pair, so |D(V)|≤|V|+3 choose(|V|,2). Start with V=S, with f≤c√L. Designate the rich blocks for C₀=D(S) as exceptional. With prescribed absences T, use C₀=D(S)∪T throughout, with T excluded from every candidate set. Their number E is O(ℓ⁶).

Visit these exceptional blocks once. If one is not already met by V, adjoin a site of the block outside D(V). This is always possible: at every stage |V|≤c√L+E and E=o(√L), so |D(V)|≤(3c²/2+o(1))L<h. With both colors, |D(V)∪T|≤(1−δ+o(1))L<h by the stated hypothesis. Every newly adjoined point creates no triple with two earlier sites. Consequently V remains k-free if S was k-free. Every exceptional block is now met. The new forbidden sites obey
$$
|D(V)\setminus D(S)|\le E+3fE+3\tbinom E2=o(L/\ell).
$$
Indeed ℓ⁷/√L→0 and ℓ¹³/L→0 under L≥ℓ¹⁶.

In the two-color case the set of new forbidden sites can only decrease upon adjoining T to both the initial and final forbidden sets. Each nonexceptional block contains at least ⌊h/ℓ⌋ sites of H by dividing it into successive ℓ-windows with its own step. Initially fewer than T of those sites can have been in D(S). The last bound shows that **at least h/(3ℓ)** sites of H outside D(V) still lie in each nonexceptional block, for all large N.

On H outside D(V), join two distinct sites by an edge if they form a triple with a point of V. The graph has maximum degree ≤3|V|: a fixed pair consisting of one vertex and one prescribed point has at most three completions. A graph-independent subset J of this host is itself 3-free, and there can be no mixed triple between J and V. Thus V∪J is k-free.

Sample a graph-independent J with probability proportional to z^|J|, with p=z/(1+z)=1/(2(1+3|V|)). Given the statuses of all other vertices, a vertex has occupation probability p if it has no occupied neighbor, zero otherwise. Under any conditioning on absences, neighbor occupation probabilities are ≤p by averaging. The occupation probability of an unexposed vertex is therefore at least p(1−3|V|p)≥p/2. The chance of missing any fixed set of b candidates is ≤exp(−pb/2), by successive conditioning on absences. The nonexceptional blocks have b≥h/(3ℓ), while p≫1/√L. Hence pb≫√L/ℓ≫log N. A union bound over the at most N² test blocks gives some J meeting all nonexceptional blocks. This completes the lower bound.

## An explicit prescription forcing an entire interval to stay empty

Let P=4^m and a=(P−1)/3. Let D_m have the base-four digits 0 or 1 in its m positions. It has 2^m elements, ranges from 0 to a, and is 3-free: reducing a midpoint identity modulo 4 first forces the three low digits to coincide, then one divides by 4 and repeats. Every integer t from 0 to P−1 has a representation x+2y with x,y in D_m, by splitting each base-four digit into its two binary bits.

Prescribe the set
$$
S_m=(a-D_m)\ \cup\ (2a+1+D_m).
$$
Each component has diameter a and the gap is a+1, so no mixed triple occurs. Its 2√P sites lie in [0,P]. For each t=x+2y as above, the two prescribed sites a−x and 2a+1+y have the forbidden third term
$$
2(2a+1+y)-(a-x)=P+1+t .
$$
No 3-free extension can hit the entire following block of P sites. Given L choose the least m with P≥L. Then P<4L, the obstruction fits when N≥8L+1 and fewer than 4√L prescribed sites suffice. For L=4^m the example uses exactly 2√L sites. In particular 256 prescribed sites exclude an entire interval of length 16,384. The identities, exact cardinalities, freeness and universal exclusion for every extension are [kernel-checked for every m](RothForcedHole.lean).

## Consequence for actual extremal sizes

Let R=r₃(N). If L→∞ and L=o((N/R)²), there is a 3-free set maximal under inclusion in [N] of size (1−o(1))R, with an entire interval of L consecutive sites disjoint from it. For the construction above |S_m|=O(√L)=o(N/R). Behrend gives (N/R)²=o(N), so the required ambient length fits. Apply the prescribed-site extension estimate to S_m to obtain a near-extremal set containing it and extend to inclusion maximality. Every further free extension retains the forced hole. Positions of the obstruction and hole may be translated together wherever both fit. [Prescribed-site extension estimate, inequality (2)](RothExtensions.md)

For the converse type of behavior at longer lengths, [the full-retention theorem](RothSparseRepair.md) gives the actual unrestricted asymptotic cardinality under an all-step hitting constraint. The asymptotic formula for r₃(N) itself is still open. [Finite integer checks](check_roth_pinned_windows.py) reproduce the weighted occupation identities, enumerate finite extension thresholds, and test the digital obstruction directly.
