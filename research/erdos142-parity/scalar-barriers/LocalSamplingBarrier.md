# Local neighborhoods do not recover the maximum in a sparse arithmetic-progression hypergraph

Take a prime N→∞, d=d(N)→∞ with log d=o(log N), and

    p²=2d/[3(N−1)],            M=⌊Np⌋.

Retain sites of the cyclic group of order N independently with probability p. Join three distinct retained sites by an unordered hyperedge when they form a three-term arithmetic progression. Compare this hypergraph C to the random hypergraph E on M vertices in which every triple is independently present with probability d/binom(M−1,2). For either graph only incidences are visible. The arithmetic labels of the sites are discarded.

Fix 0<ε<1/4. For every integer radius r≥0 such that (2d)^r≤N^(1/4−ε), the two rooted radius-r neighborhood laws have total variation distance O(N^(−cε)) for an absolute c>0 and sufficiently large N. Adjacency for vertex distance means sharing a hyperedge. A ball records its full induced hypergraph. One may attach independent uniform random marks to its vertices. Yet with probability tending to one,

    α(C) / (Np) ≥ c r₃(⌈100d⌉)/⌈100d⌉ ≥ exp(−O(√log d)),
    α(E) / M ≤ 4 √(log d / d).

Here α is the maximum number of vertices containing no hyperedge. Thus the accessible neighborhoods approach one another even as the ratio between the two optimal densities grows by at least d^(1/2−o(1)). In particular incidence-only bounded-radius algorithms on the arithmetic input miss this ratio even if designed solely for that input. Independent vertex randomness is allowed. This concerns recovery from neighborhoods, and leaves open the value of r₃.

The comparison addresses a possible use of the [effective-length estimate](https://github.com/Deldor14/open-math-agents/blob/68cd54337b3e1a61aeca710263c2e0f012292c8c/research/erdos142-hinge/RothEffectiveLength.md) for sparse interval samples. The cyclic group gives a spatially homogeneous neighborhood law. The boundary of an interval affects the law of the root, so the local comparison here is stated for the cyclic host.

## Counting the possible tree neighborhoods

Use a rooted loose ternary hypertree T, whose bipartite vertex-edge incidence graph is a tree, with e edges, v=2e+1≤B vertices, and I vertices at distance strictly less than r. For this paragraph fix r≥1 and the root site in the cyclic group, conditioned to be retained. A vertex of the full host has 3(N−1)/2 incident edges when N>3. Each distinct triple has just one midpoint, although each site can also serve as an endpoint.

For a fixed choice of the midpoint of each of the e abstract edges, the midpoint equations with the fixed root have N^e assignments: each new edge through one old site has one freely chosen variable among its two new sites. The proportion with a collision or an unintended progression among its vertices is O(B³/N), uniformly in T. Indeed any nonzero linear combination of s≥2 selected edge equations has support at least four. In the selected incidence forest with c components there are 2s+c vertices and the sum of their degree excesses above one is s−c. Hence at least s+2c degree-one vertices have nonzero coefficients in the combination. A single row has support three and cannot describe a different midpoint on the same triple for N>3. Thus each collision or unintended triple equation is independent of the tree equations. Fixing the root creates no new such dependence since all these rows have coefficient sum zero. The union bound over O(B³) candidates proves the proportion. In particular the count of valid labelled rooted embeddings is (3N)^e(1+O(B³/N)).

For a valid embedding, condition on the v−1 nonroot images being retained. Outside this set F there are O(B²) individual sites that could complete an additional edge with two sites of F; it is sufficient that all be absent. Only such edges incident to an interior vertex need be forbidden. The upper estimate on the probability of the correct ball may simply ignore these sites. For additional edges meeting exactly one interior vertex and no other site of F, let G be the ordinary graph on sites outside F whose candidate pairs complete such an edge. Then

    |E(G)|=I·3(N−1)/2+O(B²),       maxdeg G≤3I.

Each anchor contributes the full number of incident triples up to O(B) exclusions. Two distinct anchors share O(1) candidate pairs: in the two unknown endpoint variables the possible coefficient rows are (1,1), (1,−2), (−2,1). Equal rows would force equal anchors, and distinct rows have nonzero determinant in the prime field when N>3. The codegree bound three gives the maximum degree of G.

Write μ=p²|E(G)|. The probability that no edge of G has both endpoints retained is bounded above by exp(−μ+O(B²Np³)) by Janson's inequality, since an intersecting pair of edges uses three sites. The lower bound (1−p²)^|E(G)| follows from Harris' inequality. Adding the requirement on the O(B²) individual sites costs at most the relative factor (1−p)^O(B²) in the lower bound, again by Harris. The resulting probability is

    exp(−dI+O(B²Np³+B²p+BNp⁴)).

This is uniform even when the event itself has small probability. [Janson and Harris inequalities, proof and hypotheses](https://yufeizhao.com/pm/probmethod_notes.pdf)

Divide the count of successful labelled embeddings by |Aut(T,root)|. The resulting probability differs from

    (2d)^e exp(−dI) / |Aut(T,root)|                                      (1)

by a relative factor exp(O(B³/N+B²Np³+B²p+BNp⁴+e/N)). The e/N term accounts for using 3N instead of 3(N−1). Formula (1) is the probability of this ball in the rooted ternary branching tree in which each vertex has Poisson(d) new edges, each leading to two new vertices. Permuting equal subtrees, unordered pairs and incident edges gives precisely the indicated automorphism divisor. Trees of height below r are included, with all their vertices then interior.

For E, root at any fixed vertex. There are (M−1)_(v−1) possible injective assignments of the other vertices (falling factorial). Each prescribed edge costs q=d/binom(M−1,2). The number of unwanted edges touching an interior vertex is I binom(M−1,2)+O(B²M) after excluding tree edges and counting overlaps. Edges wholly confined to the boundary add at most B³ potential exclusions. Their independent absence gives (1) up to a relative factor exp(O((1+d)B²/M+Bd²/M²)), for B≤M/2. This also accounts for the finite population correction in the injective assignments and the normalization of q.

Set B=⌊N^(1/4−ε/2)⌋. Both relative errors are O(N^(−ε+o(1))) after subtracting one. The expected size of a branching ball is at most 2(2d)^r for d≥1. By Markov's inequality the branching law puts O(N^(−ε/2)) mass on balls larger than B. Summing the relative comparisons over all tree shapes of size at most B bounds the total variation distances to the branching law, including the mass of all nontrees. Radius zero is immediate. Adding independent marks is a common randomization and cannot increase total variation distance. The cyclic proof used a retained root at a fixed site. To use a uniform vertex of the realized nonempty graph, the change in the distribution of the sampled graph is the bias by its size; its total variation effect is O((Np)^(−1/2)) by the binomial variance, with a negligible empty-graph probability.

## Independence in the two hosts

Put m=⌈100d⌉ and L=2m−1. An optimal progression-free subset of [0,m) of size r₃(m) remains free of modular midpoint triples modulo L: the two sums in a midpoint equation both lie between 0 and 2m−2. Inside [0,⌊N/2⌋) take only residues from this alphabet. A modular progression modulo N in this arc is an integer progression. Reducing it modulo L places all its sites in a single residue of the alphabet. For sufficiently large N there are at least Nr₃(m)/(3L) eligible sites and at most r₃(m)(N/L)² eligible triples, by choosing the midpoint and one endpoint in their common fibre. After retention discard at most one site per present triple. The expected independent set size is at least

    (Np r₃(m)/L) [1/3−Np²/L] ≥ Np r₃(m)/(4L).

Changing one site changes the maximum by at most one. The independent-resampling variance bound gives Var α(C)≤Np(1−p), so at least half this expectation lower bound holds with probability tending to one. Here r₃(m)/m≥exp(−O(√log m)) by Behrend, and Np=N^(1/2+o(1)). [Behrend's construction](https://doi.org/10.1073/pnas.32.12.331)

For E the expected count of an independent set of size l is binom(M,l)(1−q)^binom(l,3). At l=⌈4M√(log d/d)⌉ its logarithm is at most l[log(eM/l)−q(l−1)(l−2)/6], which is ≤−l log d for sufficiently large N. This proves the upper bound with exponentially small exceptional probability and also the corresponding expectation bound.

## Consequence for algorithms using only local incidences

Let a selection rule at each vertex use its marked radius-s ball and shared deterministic parameters N,d. Suppose it returns an independent set on the arithmetic input with probability one. It need not have any feasibility guarantee on E. The event that a selected vertex lies in a fully selected hyperedge depends only on its radius-(s+1) ball. If (2d)^(s+1)≤N^(1/4−ε), total variation makes its probability on E at most O(N^(−cε)). Delete every such vertex from the output on E. What remains is independent. The selected fraction and the bad-vertex fraction therefore bound the expected selected density on the arithmetic input by

    4√(log d/d)+O(N^(−cε)).

Since d=N^o(1), the error is negligible compared with √(log d/d). This gives a lower bound on the radius needed by any isomorphism-invariant rule of this form for a constant-factor approximation. It applies to the incidence graph with independent marks; a rule given the arithmetic coordinates can use the residue construction directly.

## Verification and arithmetic marks

[LooseForestRows.lean](LooseForestRows.lean) verifies the forest support bound for active edge equations and the cancellation of the fixed-root coefficient. [SparseSampling.lean](SparseSampling.lean) verifies the finite fibre count, no wrap in a half interval and deletion of at most one vertex per edge. The probability comparisons and the conclusion about algorithms are written proofs. A [companion argument with arithmetic residues](LocalResidueInformation.md) gives the number of residue classes needed by local selection rules when the midpoint is distinguished and the true residues are supplied.
