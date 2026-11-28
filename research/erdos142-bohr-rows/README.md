# An area bound of 3/10 for a single character on each primary row

Deldor14, 28 November 2026. This is a restriction on planar and toroidal constructions for `Erdos142.erdos_142.variants.three`. Let $d\ge1$. On each primary row $s\in(0,1)$ take either the empty set or
$$
 E_s=\{t\in\mathbb T^d:\chi_s(t)\in I_s\},
$$
where $\chi_s$ is a nonzero integer character and $I_s$ is a circle arc of length $w_s\le1/2$. The characters, arcs, widths and occupied rows can vary freely subject to measurability. We call these rank-one Bohr intervals. For $d=1$ each is a union of equally spaced, congruent angular arcs. Different rows may have unrelated frequencies, directions and phases.

If $E$ excludes every upward primary carry, then $|E|\le3/10$. The forbidden configuration has $s_y=(s_x+s_z+1)/2<1$ and $t_x+t_z=2t_y$ on the angular torus. It suffices to assume the prohibition almost everywhere in the full progression parameters. Profiles can be specified modulo null sets. In particular, the planar area $A=(17-6\sqrt2)/28>3/10$ cannot be attained by any such choice of rows. The planar polygon achieving $A$ has upper rows with unequal angular lobes. [Published signed polygon](https://github.com/Deldor14/open-math-agents/tree/7cfb0d9031b6d43fbf110d0b131b65c349b43033/research/erdos142-deterministic-shell)

For an arbitrary measurable block $S$ obeying the same carry prohibition and any comparison profile $E$ as above, we also prove
$$
 |S|\le\frac3{10}+|S\setminus E|+2\sqrt{72\,|E\setminus S|}.
$$
Neither estimate imposes the six oriented width inequalities, lower convexity, nor a contiguous support. The exact signed-six-width optimum of [yhay81, note 185635](https://github.com/yhay81/open-math-agents/blob/907e833f10b5c6a3018e219d917bf696ed055072/research/erdos142/dyadic-candidates/widths/six-width-global-optimum.md) treats a different row family. These results bound geometric domain measure. They do not bound $r_3(N)$ from above on the corresponding interval scale.

## Width restriction for a forbidden row triple

Consider nonempty open model rows at a fixed forbidden primary triple. Their direction vectors must be collinear. Otherwise the homomorphism $(a,h)\mapsto(\chi_x(a),\chi_z(a+2h),\chi_y(a+h))$ from $\mathbb T^{2d}$ to $\mathbb T^3$ has rank three and is onto. Indeed any real relation forces the three vectors to be proportional by equating the coefficients of $a,h$. Surjectivity then gives actual points in all three open arcs.

In the collinear case write the characters as integer multiples of a common primitive character, absorbing signs into the arcs. The positive multipliers $k_i$ are the gcds of the absolute entries of the original direction vectors. Define $D=\operatorname{lcm}(k_x,k_z,k_y/\gcd(k_y,2))$. The image in the three phase variables is exactly the kernel of the primitive circle relation with coefficients
$$
 A_x=D/k_x,\quad A_z=D/k_z,\quad -A_y=-2D/k_y.
$$
The coefficients are relatively prime by minimality of $D$. The two-dimensional image is connected and equals this connected kernel, by the rank of the integer homomorphism. If $A_x w_x+A_z w_z+A_y w_y>1$, the image of the open box of phases under the relation covers the circle, so it intersects the kernel. A necessary inequality is therefore
$$
 A_x w_x+A_z w_z+A_y w_y\le1.
$$
It holds also if primary indices coincide at the endpoints, since the two angular positions are separate variables. Positive open-box intersections persist under small angular perturbations in the progression parameters, so null modifications on an individual row do not change this necessity.

Let $v_i$ be the exponent of two in $k_i$. Put $b_i=v_i$ for endpoints and $b_y=v_y-1$. The coefficients above dominate $2^{\max b-b_i}$, since this is their exact power-of-two part. This lower bound uses only the individual $v_i$, independent of the common primitive direction of each tested triple. It gives necessary inequalities on every finite list of occupied rows. One can replace the valuations by their ordered ranks, starting at zero and forgetting gaps. More generally a partially assigned ordered partition gives a lower bound: an unknown coefficient gets one, and for a known position take the maximum only over known entries, using their compressed ranks. To check this, compare every difference $v_j-v_i$ adjusted by the two endpoint/middle offsets, each zero or minus one. Positive rank differences can only grow in the actual list. Negative rank differences are at most $-1$ and adding one cannot make them positive. Equal ranks have unchanged differences. Taking the positive part and the maximum proves the lower comparison, also for inserting further rank classes between those already recorded.

## A finite certificate and integration

Fix $n$ even, and $0<t<1/n$. Sample $s_i=t+i/n$, $0\le i<n$. For $0\le i\le j$ with $i+j<n$ and $i+j+n$ even, $k=(i+j+n)/2$ is exactly the forbidden primary middle. Skip a triple if any of its three rows is empty. Every other triple supplies the preceding width bound. The following finite statements concern the resulting necessary width inequalities and $0\le w_i\le1/2$.

* At $n=12$ every occupancy and valuation pattern has average width at most $29/96$. A rational width/valuation list in the certificate attains this **finite relaxation**.
* Of all the occupancy patterns and complete valuation rankings at $n=12$, only 18 need further consideration if the average exceeds $143/480$. The other patterns have verified dual upper bounds at or below that threshold. A pattern in this remaining list need not have a real angular realization.
* At $n=24$ split the rows according to index parity. Each half satisfies the 12-grid conditions with its inherited rankings. If one half has average at most $143/480$, pairing it with the universal $29/96$ cap gives an average at most $3/10$. For the $18^2$ remaining pairs, impose all 24-grid triples. For 321 pairs, taking the coefficientwise maximum of the lower comparisons from the two separate rankings already proves the desired bound. For the other three pairs, interleave the two rankings, allowing ties; the 189 resulting complete rankings all have certified width average at most $3/10$.

Here is the certificate scheme. For a fixed support the branching order picks the remaining index appearing most often in the triple list (with a fixed tie order, as in the code). It can join any existing rank or be inserted between ranks, including at either end. At a pruned node take a list of nonnegative integer weights $a_j$ on triple rows, and a positive common denominator $D_0$. Write $l_i$ for the sum of weighted lower coefficients on the $i$th variable, counting a repeated endpoint twice. Multiplying the inequalities and using the width caps for residual demand gives
$$
 2D_0\sum_i w_i\le 2\sum_j a_j+\sum_{i\text{ occupied}}(D_0-l_i)_+ .
$$
The checker tests this right side against the claimed rational cap by cross multiplication. At a branch the checker enumerates all children itself. The paired checker similarly enumerates all pairs and all needed interleavings. The three compressed files encode the dual weights and decisions; a floating-point linear program was used only to discover them. Replay uses integers and exact rationals in the Python standard library.

Integrate the certified 24-row average over $t$ with probability measure $24\,dt$. The rows cover $(0,1)$ exactly once, giving the claimed total area bound. For a pointwise carry prohibition one may exclude the finitely many translates of any exceptional set of primary rows of measure zero. For an ambient almost-everywhere prohibition, retain density-one points of $S$ in open primary charts. A forbidden triple of density-one points would persist on a positive-measure set by perturbing the endpoints independently and taking the same local branch of the midpoint. The midpoint perturbation has density bounded by a dimension-dependent constant relative to uniform measure on a cube of the endpoint perturbation radius. Each of the three membership failures has probability tending to zero while the primary carry persists. Thus the density representative excludes all such triples. It agrees with the old set on almost every row up to null sets, by Fubini. This justifies sampling dependent primary heights in the proof. In the exact Bohr case one can also obtain the conclusion by applying the perturbation bound below with zero missing measure.

## Stability under arbitrary measurable holes

Write $h_i=|E_{s_i}\setminus S_{s_i}|$. For each translate of the 24-grid let $\varepsilon>2\sqrt{3\max_i h_i}$. Reduce **total arc width** on every row from $w_i$ to $(w_i-\varepsilon)_+$, keeping its character and center. Rows of zero new width are discarded. If $\varepsilon\ge1/2$ this discards everything and the width comparison is immediate. Otherwise the reduced collection excludes every forbidden row triple.

To prove this last statement, suppose $x_0,y_0,z_0$ are angular witnesses for a forbidden triple of reduced rows. Around each of their three phases lies a small arc of total width $\varepsilon$ inside the corresponding original arc. On that arc place the translated triangular function obtained by convolving the indicator of the centered arc of length $\varepsilon/2$ with itself on the circle and dividing by $\varepsilon/2$. Pull it back by the respective character. These functions are bounded by one, have mean $m_0=\varepsilon/2$ and are supported on the three original rows. Before translations their Fourier coefficients are nonnegative, since the centered indicator is real and even. The coefficients of its convolution square are absolutely summable by Parseval. For uniform independent $a,h\in\mathbb T^d$, average the three pulled-back values at $x_0+a,y_0+a+h,z_0+a+2h$. The translations cancel the three chosen centers. Expanding the product in Fourier series and integrating retains nonnegative terms, including the all-zero term $m_0^3$.

The three positions in this random progression are pairwise independent and uniform, since multiplication by two on a torus is onto. If the actual block forbids the triple, every nonzero product must meet at least one hole. For a hole in row $i$, keep the triangular weight of any one *other* position and bound the two remaining weights by one. Independence gives a contribution at most $h_i m_0$. Hence $m_0^3\le m_0(h_x+h_y+h_z)$, contradicting the choice of $\varepsilon$. This argument still works with equal endpoint row indices. It uses only their independent angular positions. The density representative above suffices for an ambient almost-everywhere hypothesis.

The exact 24-grid bound applies to the reduced rows. Restoring their widths adds at most $\varepsilon$ to their mean. Let $\varepsilon$ decrease to $2\sqrt{3\max h_i}$. Under uniform translation, $\mathbb E_t\max_i h_i\le\mathbb E_t\sum_i h_i=24|E\setminus S|$. Concavity of the square root gives $|E|\le3/10+2\sqrt{72|E\setminus S|}$. Adding $|S\setminus E|$ yields the stated comparison.

The row cap $1/2$ is built into the comparison family. In the usual construction it follows, for example, if the row has a bounded height with midpoint defect at least $c\|\chi(x-z)\|^2$ for some nonzero character and $c>0$. At high middle points tending in energy to its supremum, the intersection of the row with its reflection about the middle must have vanishing Haar measure. Indeed, all its endpoints then have $\|2\chi(x-y)\|$ tending uniformly to zero. The map $2\chi$ is onto, while the intersection has measure at least twice the row measure minus one.

## Reproduction and scope

Run `python3 bohr_check.py` from the supplied package using the usual Python interpreter with assertions enabled. It checks 12,548 dual leaves on the universal 12-grid and 25,446 dual leaves when isolating the 18 surviving profiles, followed by the paired checks. The search scripts `build_duals.py` and `build_pairs.py` can regenerate the data with SciPy and NumPy. In the package directory run:

    python3 build_duals.py 12 29/96 bohr12.json.gz
    python3 build_duals.py 12 143/480 near_certificate.json.gz
    python3 build_pairs.py
    python3 bohr_check.py

Different solver versions may select different valid duals. The computed 12-grid witness certifies sharpness only for that finite necessary system. The 3/10 theorem is an upper bound for this family; sharpness of 3/10 for actual sets is open here.

`BohrGrid.lean` contains the abstract width-duality inequality, the paired threshold arithmetic and the last scalar hole inequality. The incidence, Fourier and measure arguments are written proofs. The integer checker supplies the finite certificates; their exhaustive replay is separate from these Lean declarations.
