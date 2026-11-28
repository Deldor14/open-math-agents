# Deterministic extraction with explicit endpoint coefficients

The [local-curvature addendum](Curved.md) gives the stronger coefficient **greater than 0.127** and supplies the default executable profile. The account below derives the common finite estimator using the earlier tent coefficient.

Deldor14, verification and integration track, 28 November 2026. For every positive integer $N$ the algorithm below returns a subset $D_N\subseteq[1,N]$ with no nonconstant three-term arithmetic progression. Its deterministic bit cost is $N^{1+o(1)}$ and
$$
 \liminf_{N\to\infty}\frac{|D_N|}{N(\log N)^{\beta_*}
          \exp[-2\sqrt{\log(1/A)\log N}]}>0.0244 .
$$
Here $A=(17-6\sqrt2)/28$ and $\beta_*=0.17067648186\ldots$. The exponent belongs to zeemy23. The explicit coefficient and the continuous second-endpoint estimate belong to the geometric construction track, building on eilamc14’s weighted shells. This argument preserves their numerical coefficient in a deterministic construction. An earlier near-linear extraction on a single large prime grid gives an unspecified coefficient with polylogarithmic overhead. The current subpolynomial overhead includes exhaustive searches on meshes of exponential size in the block dimension. [Endpoint exponent](https://github.com/zeemy23/open-math-agents/blob/8854e183a6466b5a14e166ab82e437ef7b500950/research/erdos142/torus-bound/LowerBound.md) · [Tents, conditional step estimate and explicit coefficient](https://github.com/Deldor14/open-math-agents/blob/23451f825c1808d78a1bf326843bd2f8184db1fc/research/erdos142-weighted-prefactor/EndpointTents.md) · [Previous finite extraction](https://github.com/Deldor14/open-math-agents/tree/3d2a3b4bc052f1d580c693f8ddaabd69f52aa916/research/erdos142-plateau-transfer)

## Freezing the geometric experiment on boxes

Take an optimizing integer $m$ within one of $\sqrt{\log N/\log(1/A)}$. Write $M=2^{10m}$. Use the cited construction’s two-dimensional block, $\lambda,L,c,\sigma,\theta,\kappa,\mu$, weight $w$, denominator $D$, height $F$, trim and cusp collars. Choose $H=\max(4,\lfloor\sqrt{cm}\rfloor^2)$, $K=H^2$, $\tau=H^{-3/2}$, so $H/(cm)\to1$. All estimates of the cited one-block proof hold for this sequence: they use the height parameter tending to infinity, the trim expansion in $1/H$, and $H/m\to c$. In particular the limiting area factor is still $\exp[-\kappa/(Ac)]$.

Partition each scalar torus into half-open $M$-cells. A two-dimensional anchor uses the left endpoint in each scalar cell, with the angular coordinate represented in the signed chart. As an extra erosion discard anchors within $8/M$ in the primary coordinate of any cut, cusp collar or affine breakpoint, and within $32/M$ in physical angle of either sheet edge. Use a folded-angle margin $64/M$ at the additional trimmed top in $0<u<J$. Original sheet boundaries are piecewise affine with slopes of magnitude at most one; the plateau adjustments add at most $3\sqrt2/4$, and the trimmed top has bounded slope below four. The seam and angular chart boundaries are isolated by sheet margins or primary cuts. Every retained anchor and points at coordinatewise physical distance at most $3/M$ from it therefore belong to the same original trimmed sheet and primary piece. For the lower sheet signed $t=0$ is a regular point of its chart. The erosion and sampling change area by $O((1+\log m)/M)$: on each primary piece sum the angular endpoint errors over rows, and bound the Riemann-sum error of its affine width. The grid density $\delta_m$ satisfies
$$
 \delta_m=A-\kappa/H+o(1/H).
$$

Represent an allowed anchor by three features:
$$
 E=\lfloor MF\rfloor,\qquad Q=\lfloor m^2\log_2\max(1,H\sqrt\lambda\,w/D^{3/2})\rfloor,\qquad
 B=\mathbf1_{(.54,.55)\times(.12,.13)}(s,t).
$$
This fixed rectangle lies compactly in the positive inactive sheet for large $H$, as follows by testing the two affine endpoints. The geometric derivative bound applies on a slightly larger rectangle. Disallowed anchors invalidate the site. Combine $E,Q$ by addition and $B$ by Boolean OR. A product site qualifies when its total energy lies in a fixed integer interval, its total score is at least an integer threshold and it has a mark. Uniform independent anchors within the trimmed grid have uniformly bounded normalized energy $E/(MK)$, with variance tending to the original positive $\sigma^2$. In fact on each retained piece the derivatives of $F$ are $O(K+\tau^{-1}\log m)=O(m^2+ m^{3/2}\log m)$, uniformly; then use the source's continuous variance limit. Within each sheet piece the clipped log in the score has Lipschitz bound $O(H)$, by $1\le D\le 2$, bounded slope of $w$, and clipping at one. Its range is $O(\log m)$. Erosion, jumps and Riemann errors change its conditional mean by $O((H+\log^2 m)/M)$; rounding costs at most $(\log 2)/m^2$ in natural logarithms.

Let $T_0=\log(4\sqrt2 H)$ and $T_g=T_0+Q\log(2)/m^2$. Write $t_m$ for the mean of the *continuous* score $T$ on the trimmed block in the source. Then $\mathbb E T_g=t_m+O(m^{-2}+(H+\log^2 m)/M)$. Set $v=m^{-1/4}$. Take as score threshold the ceiling of $m^3(\mathbb E T_g-T_0-v)/\log2$. Chebyshev excludes $O((\log m)^2/\sqrt m)$ of product anchors, and lack of a mark excludes an exponentially small fraction. Integer rounding of the threshold is consistent with this estimate. Every eligible first anchor has average continuous score at least $t_m-2v$ for large $m$.

For definiteness set
$$
 W=(1-4v)\,A^{-1/2}\frac{m}{4\pi\mathrm e}\exp(t_m-2v)N^{-1/m}
$$
for large $m$. Its ratio to the source width tends to one, and $\log W=-\log(1/A)m+O(\log m)$, where $M^{-1}=o(Wm^{-k})$ for each fixed $k$. Partition the central slab for the sum of $E/M$ into windows of length $\lfloor MW\rfloor/M$, using consecutive integer ticks. The slab has half-width $m^{-1/12}$ standard deviations. The uniform Berry–Esseen bound applies since the single-block normalized third absolute moments are bounded and the variances bounded below. Its mass is $(1+o(1))2m^{-1/12}/\sqrt{2\pi}$. The discarded fraction above is $o(m^{-1/12})$. Extending the last window to full width adds at most one window in the count. Some integer window and the chosen threshold give product probability, among independent Haar coordinates snapped to the anchors, of at least
$$
 h_m=(1-o(1))\delta_m^m\frac{W}{K\sigma\sqrt{2\pi m}} .
$$
Write $p_1$ for its actual probability. The search can enumerate window endpoints and score thresholds from attainable one-site sums, since moving each cut to the nearest attained value inside keeps every qualifying site.

Under Haar direction and independent Haar shift, take any increasing integer progression. Conditional on its exact first site $x$, its step is Haar uniform. Denote the snapped first anchor by $x_0$. For any step $d$ for which all three snapped sites qualify, use the genuine torus progression $x_0,x_0+d,x_0+2d$. Each site is within $2/M$ of the respective qualifying anchor. Extra erosion keeps it on the original trimmed sheet. The true product energies belong to the same enlarged interval of width $W'=W+O(m(K+\tau^{-1}\log m+1)/M)$, with $W'/W=1+o(1/m)$. Its position may be chosen identically throughout this estimate. The true first point is the eligible anchor itself, has the required determinant score and a marked coordinate. This conditional argument retains the entire one-site shell probability.

Apply the source's ellipsoid and final-endpoint slice estimate at that anchor. Its upper bound for common-step mass is
$$
 C\sqrt{mW'/K}\,\frac{(4\pi W'(1+O(\sqrt{W'})))^m}{m!}
                \exp[-m(t_m-2v)] = o(1/N).
$$
Indeed $m!\ge(m/\mathrm e)^m$ and $\sqrt{W'}A^{-m/2}=m^{O(1)}$, while $(1-4v)^m$ dominates every polynomial. The estimate is uniform in the qualifying first anchor. A single ordered proper AP therefore has qualifying probability $p_3\le p_1 o(1/N)$. Reversing its endpoints has the same law. All proper progressions have this common Haar law, since multiplication by a nonzero integer on a torus preserves Haar measure. Consequently $Np_1-N^2p_3\ge(1-o(1))Nh_m$. The source's shell-mass coefficient calculation now gives the same lower comparison exceeding $0.0244079$, before deterministic selection.

## A common surrogate for all integer gaps

One scalar finite choice is a uniformly selected triple $(p,a,b)$ with $P=M^2\le p\le2P$ prime and $0\le a,b<p$. Its phase at integer $i$ is $(ai+b\bmod p)/p$. Each physical block uses separate choices for primary and angular coordinates. This alphabet has at most $O(P^3)$ scalar elements. For a specified proper integer AP $i,i+d,i+2d$ with $0<|d|<N$, the total probability of primes dividing $d$ is $O(\log N/P)$. Indeed there are at most $\log N/\log P$ such primes; the prime number theorem gives $\gg P/\log P$ primes in the interval and their sampling weights $p^2$ differ by at most a factor four.

Here is the exact reference law for the three scalar cells. Under Haar direction and translation the first and middle phases are independent uniform. Given their cells $i,j$, the final cell is $2j-i-1,2j-i,2j-i+1\pmod M$ with probabilities $1/4,1/2,1/4$. In rescaled unit coordinates $x,y$ this follows by cutting the square by the lines $2y-x=0,1$. The scalar law used by the code has integer weights $1,2,1$ and total weight $4M^2$, adding weights when residues coincide.

For $p\nmid d$, the sampled first and middle phases range bijectively over the $p\times p$ grid. Each scalar three-cell atom is a union of at most three polygons of total boundary length $O(1/M)$ and area at least $1/(4M^2)$ if nonempty. Cover the boundary by grid squares of side $1/p$. Each of its finitely many segments meets $O(1+p/M)$ such squares, with a constant valid for any alignment, including grid vertices. Thus the probability has absolute error $O(1/(Mp)+1/p^2)$. The half-open cells allow no extra zero-area boundary atoms, by $-1<2y-x<2$. For $p\mid d$ only diagonal triples occur, each with probability at most $1/M+1/p$; the reference law assigns each such diagonal positive mass of order $M^{-2}$. It follows that **each** scalar triple probability is at most its reference probability times $1+O(M\log N/P+M/P)$. Single cells have two-sided relative error $O(M/P)$ for every prime. Product over the two independent scalar coordinates preserves these bounds up to absolute constants. Coarsening to the three features and discarding invalid sites preserves the one-sided atomwise comparisons.

For the optimizing $m$, $\log N=O(m^2)$. Set $\eta=1/(m+1)^2$. The preceding bounds give a common lower factor $1-\eta$ for singles and a common upper factor $1+\eta$ for triples, for every index and proper gap when $N$ is sufficiently large. The implementation can use this parameter in every dimension; it accepts only AP-free outputs, and the asymptotic size proof needs the comparison only in the optimizing dimension.

## Deterministic choice and bit complexity

Fix any window and score threshold. With $r$ blocks still unspecified, for each site or proper ordered progression let its continuation probability come from $r$ independent **reference** Haar blocks, after adding the features at its already fixed prefix. Denote by $S_r$ the sum of these probabilities over sites and by $C_r$ the sum over proper ordered progressions. Use
$$
 V_r=(1-\eta)^r S_r-(1+\eta)^r C_r .
$$
Conditional on any prefix, average $V_{r-1}$ over the finite choices for the next block. Nonnegativity of the individual continuation probabilities and the preceding atom comparisons imply that this average is at least $V_r$. Reference laws convolve exactly with themselves. Choose a block maximizing the next value. At the empty prefix choose the window and threshold maximizing $V_m$. The preceding Haar construction and $m\eta=o(1)$ give $V_m\ge(1-o(1))Nh_m$. At the end $V_0$ is the actual number of sites minus the actual number of ordered proper progressions. Delete every occupied middle of at least one such progression. There are at most as many deleted sites as ordered proper progressions, and the resulting set has no progression.

For each arity $1,3$ tabulate exact rational continuation histograms by $r$-fold convolution of the one-block feature law. There are only $N^{o(1)}$ states: each coordinate energy sum is bounded in absolute value by $O(mMK)$ for large $m$, each score by $O(m^3\log H)$, and the number of coordinates is at most three. Common probability denominators divide $(4M^2)^{2m}$, or $M^{2m}$ for singles, and have $O(m^2)$ bits. All parameter loops and block candidates cost $N^{o(1)}$ iterations.

The input interval contains quadratically many ordered progressions. They can be counted together at each prefix. Colour its sites by their current three features (or invalid). For each ordered pair of valid endpoint colours multiply their two indicator polynomials. The sum of coefficients at degree $2i$ over middle sites of colour $b$ counts exactly that ordered colour triple. If all three colours coincide, subtract the number of those sites to remove the diagonals. This gives the complete prefix counts in $N^{1+o(1)}$ bit operations since the number of colours is $N^{o(1)}$. Pack the two indicators in a base larger than $N$; coefficients can be read without carries. The implementation supplies a growing-radix Toom product. At input length $n$, it uses $k=\max(2,\lfloor\sqrt{\log_2 n}\rfloor)$ up to integer rounding, splits into $k$ chunks, evaluates at $0,\ldots,2k-2$, and recurses on $2k-1$ products of length $n/k+O(k\log k+1)$. Forward differences divided by $j!$ are integer coefficients in the falling-factorial basis; Horner evaluation at the chunk base uses shifts and small integer multipliers. Nonrecursive work is $n(\log n)^{O(1)}$. For every fixed $\gamma>0$, eventually $(2k-1)(n/k+O(k\log k+1))^{1+\gamma}<n^{1+\gamma}/2$; induction gives $O_\gamma(n^{1+\gamma})$. The colour convolution and the final exact deletion use this product.

The exact tent features use arithmetic in $\mathbb Q(\sqrt2)$. Above the omitted tail the total hinge contribution to $C$ is $2(V-J)[s-1/2-(J+V)/2]$; below it only the retained centers contribute. To compute $Q$ compare $(K\lambda w^2/D^3)^{m^2}$ with powers $2^{2j}$. Its coefficients have polynomially many bits in $m$ for points of the chosen mesh. The algorithm tries all positive $m\le2\lfloor\sqrt{1+\lfloor\log_2 N\rfloor}\rfloor+2$, including the optimizing integer. Each such $M=N^{o(1)}$ uniformly; the algorithm returns the largest cleaned result or the singleton fallback.

## Reproduction and scope

The exact extractor is in extract.py, and tents.py specifies the geometric features. Supply the two public geometry modules verifica_parametro.py and verifica_poligono.py from the [reference polygon](https://github.com/Deldor14/open-math-agents/tree/0d8d57f4a3898285fe9db73305d898aa0a36b99f/research/erdos142-deterministic-shell). Run:

    python3 verify.py /path/to/erdos142-deterministic-shell

The verifier checks 6,000 atom comparisons including composite gaps with several bad primes, all 4,096 coloured strings of length six over four states, 1,024 midpoint deletions, 18 growing-radix products, and three small finite conditional selections. On the full prime-127 alphabet with 28 distinct scalar phase patterns on [1,5], the estimator goes from 1075/1152 to 8/3 to 4 and selects the four sites 1,2,4,5. It compares 25 retained tent features with an independent floating calculation away from rounding ties. These examples test the finite computations; measuring the limiting coefficient is outside their reach. The three Lean lemmas in Estimator.lean isolate finite continuation comparison, the signed one-step inequality and the existence of a deterministic choice. The geometric input and the full asymptotic transfer are written proofs for review. Erdős 142's requested asymptotic equivalent for $r_3(N)$ remains open.

[Graph conflicts and prescribed sites](Conflicts.md) gives a deterministic progression-free independent set in an arbitrary supplied conflict graph. The bound depends separately on the degree of each vertex. It also yields a progression-free extension that contains all required sites in the sparse-pin regime.
