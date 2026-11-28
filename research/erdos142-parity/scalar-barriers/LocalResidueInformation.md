# How many arithmetic residues suffice for local recovery in a critical sample?

Let N=QP with P a prime coprime to Q and gcd(6,N)=1. Allow Q=1. Suppose d→∞, log d=o(log N), and Q≤C d for a fixed C. Sample sites of the cyclic group of order N with independent probability p, where p²·3(N−1)/2=d. An edge consists of three distinct sites in arithmetic progression. At every vertex reveal its residue modulo Q, and at every edge reveal which vertex is the midpoint. The actual positions within a residue remain hidden. Independent random marks at vertices are allowed. The optimum has density comparable to δ=r₃(⌈d⌉)/⌈d⌉ in expectation by the interval upper estimate and the single-arc lower bound proved below and in the companion note.

Fix ε>0. Consider a rule that always selects an independent set and uses only radius-s neighborhoods of these marked incidences, where (2d)^(s+1)≤N^(1/4−ε). In the range d/Q→∞ its expected fraction of sites selected, among retained sites, is

    O( sqrt(log(2+d/Q)/(d/Q)) ).

Consequently, recovering a fixed positive fraction of the optimum in expectation requires

    Q ≥ c d δ² / log(2/δ).

In particular the logarithm of the number of residue classes needed is (1−o(1)) log d. Conversely, for any available divisor Q between 10d and 20d, a radius-one rule observing these same marks achieves a constant fraction of the expected optimum. This is a statement about the residue information modulo a divisor of the host and the specified class of local algorithms. Other encodings of arithmetic information are outside its scope.

## A random comparison with the very same marks

Put M=Q⌊Np/Q⌋, and split M vertices into Q equal types modulo Q. For each triple of distinct vertices, and separately for each of its possible choices of midpoint satisfying the congruence modulo Q, include that oriented edge independently with probability

    q=2dQ/(3M²).

Several choices can occur on a triple of a single type; the records keep their distinguished midpoints. One can discard graphs with repeated oriented choices on the same triple at a total probability cost O(d²/M), by summing the probabilities of these pairs. Indeed all three types must coincide, giving O(M³/Q²) potential repeats. This model need only reproduce marked neighborhoods; it can impose far fewer integer constraints on a global assignment of coordinates.

The two marked radius-r laws, with (2d)^r≤N^(1/4−ε), are at total variation distance O(N^(−cε)) for an absolute c>0. Here the root type is uniform. Conditional on its type, fix a tree shape with v≤B, e=(v−1)/2 edges and I interior vertices, now with all type marks and midpoints specified. If any edge violates the congruence its probability in each law is zero. Otherwise the common branching-tree probability is

    (2d/(3Q))^e exp(−dI) / |Aut(T,root,types,midpoints)|.

In the arithmetic host the number of possible embeddings before excluding collisions and unintended progressions is P^e, since the free variable of each new edge has its residue already specified. Reducing modulo P leaves an independent uniform field variable per edge, by the Chinese remainder theorem. The linear forest argument of [the unmarked comparison](LocalSamplingBarrier.md) bounds the relative exclusions by O(B³/P). For a valid embedding the outside-pair void calculation of that note applies to the full cyclic host. The candidate-pair overlaps remain O(B²) because the determinants of distinct coefficient rows are ±3 and gcd(3,N)=1. Two-sparse variable inequalities and completion of a midpoint use invertibility of 2. Thus the other relative errors are as in the unmarked case. Multiplying by p^(2e) produces the stated prefactor, up to exp(O(e/N)).

In the independent model the number of injections matching all types is (M/Q)^(2e) exp(O(B²Q/M)). Conditional on the tree edges, all other feasible oriented edges are independent. The number of feasible oriented triples at one specified vertex is 3M²/(2Q)+O(M), uniformly in its type. Indeed fixing the vertex as midpoint gives half the ordered endpoint-pair count, and fixing it as an endpoint gives the ordered count with a distinguished midpoint. Each ordered relation allows Q choices of one type and then determines the other type. Repeated vertices exclude O(M) choices. At I vertices, multiplicity of counting and prescribed tree edges contribute O(B²M+B³) to the error. Requiring all extra edges touching the interior or lying wholly in the boundary to be absent consequently costs

    exp(−dI+O(dQB²/M + B d²Q/M²)).

These estimates hold uniformly at B=⌊N^(1/4−ε/2)⌋, since Q,d=N^o(1) and M=N^(1/2+o(1)). The common branching law has Poisson(d) child edges per vertex as before. Equivalently, given a parent type choose its incidence role uniformly among the three positions with unordered new vertices and a uniform free type for the two new positions subject to their relation. Truncating by the expected tree size and comparing probabilities shape by shape gives the total variation claim. The same comparison applies after adding independent vertex marks. [Details of the unmarked calculation](LocalSamplingBarrier.md)

Inside a single type the independent model contains the binomial ternary hypergraph with edge probability 1−(1−q)³≥2q for sufficiently large N. Its mean degree is at least a fixed multiple of t=d/Q. The first-moment bound on independent sets shows that its largest free fraction is O(√(log(2+t)/t)) with exceptional probability at most exp(−c (M/Q)√(log t/t) log t) for all large t. The union bound over Q types preserves this estimate up to the factor Q. Any independent set must satisfy every within-type constraint. Applying the local comparison to the event of a selected vertex and the event of a selected vertex in a fully selected edge gives the asserted algorithmic bound, as in the companion proof. It also applies when feasibility is guaranteed only on the arithmetic input.

The arithmetic optimum in the cyclic sample is at least cδ in expected density. The half-interval and residue deletion lower proof in the companion note applies to this composite N as well. Its scale ⌈100d⌉ can be replaced by ⌈d⌉ at the cost of a constant by monotonicity and the bounded ratio of lengths. For a constant fraction of this lower bound one must have t/log(2+t)=O(δ^(−2)). Since t/log(2+t) is increasing and log(2+Cδ^(−2)log(2/δ))=O(log(2/δ)) for fixed C, inversion gives the stated necessary bound. Bounded t already satisfies it. Finally Behrend gives log(1/δ)=O(√log d).

## Sufficiency at a modulus of order the mean degree

Suppose 10d≤Q≤20d and put m=(Q+1)/2. Take a cyclically progression-free alphabet D of size r₃(m) modulo Q by embedding an optimal subset of [0,m). Every midpoint equation in these digits has each side at most 2m−2=Q−1. Select every retained site whose type is in D and then remove the midpoint of every present edge among the selected sites. This is a radius-one rule with a precomputed finite alphabet. Every selected progression before deletion has one common type at all three sites. Each type is a coset of the subgroup of order P, whose ternary progression hypergraph has P(P−1)/2 edges. Thus the expected number selected after deletion is at least

    Np |D|/Q · [1−(P−1)p²/2] ≥ (9/10) Np |D|/Q

for all sufficiently large N in the stated range. By monotonicity |D|/Q≥cδ. The expected cyclic optimum is at most the expected interval optimum on the same retained sites, since avoiding all cyclic progressions also avoids the integer ones. The published two-sided [effective-length estimate](https://github.com/Deldor14/open-math-agents/blob/68cd54337b3e1a61aeca710263c2e0f012292c8c/research/erdos142-hinge/RothEffectiveLength.md) bounds its latter expectation by C Np r₃(b)/b, b=⌈Np²⌉. Here b and ⌈d⌉ differ by bounded factors; monotonicity and partitioning into short intervals compare the two densities within absolute factors. This proves the sufficiency conclusion. Only this comparison with the expected optimum uses the upper part of the cited estimate.
