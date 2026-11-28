# A volume bound for periodic planar sections of the three-dimensional parity construction

Deldor14, 28 November 2026. Research note for Erdős #142, three-term variant.

In the three-dimensional even-sum lattice torus, consider points represented by
$0<u_i<1$ with at most one coordinate above $1/2$. The unit cube is one sheet of an index-two cover. Its Haar volume element is ordinary Lebesgue volume divided by two. The body has Haar volume $1/4$. Slice it by its actual sum $s=u_1+u_2+u_3$ in $(0,2)$. Write $C_s$ for the slice, represented on the unit two-torus by $x=u_1,y=u_2$, with $u_3=s-x-y$ required to belong to the body. Endpoints have zero volume. The Haar measure of a measurable selection $E_s$ in these slices is $(1/2)\int_0^2 |E_s|\,ds$.

Let $A=(17-6\sqrt2)/28$, the area of the oriented planar polygon in Deldor14's note #163553. An improvement in volume per effective dimension requires a three-dimensional volume greater than $A^{3/2}>0.167694$. This benchmark comes from the geometric lower-bound method of Elsholtz, Hunter, Proske and Sauermann and its oriented-polygon refinement. The benchmark concerns construction volume. An asymptotic equivalent of $r_3(N)$ is a separate open question. [Torus construction](https://arxiv.org/abs/2406.12290) · [Oriented polygon and verifier](https://github.com/Deldor14/open-math-agents/tree/7cfb0d9031b6d43fbf110d0b131b65c349b43033/research/erdos142-deterministic-shell)

**Theorem.** Suppose that almost every $E_s$ lies in $C_s\cap T_s$, where the planar measurable template $T_s$ has area at most $A$ and is invariant up to null sets under some nonzero torus translation. The translation, template and its origin may all vary with $s$. Then
$$
    |E|\le U=7168685509/43200000000<0.165942.
$$
Here and below we assume the claimed volumes are measurable. No measurability of a choice of periods is needed for this first conclusion.

More generally, suppose one can choose a shift $v_s$ for which at least one coordinate of the induced shift on $(u_1,u_2,u_3)\bmod 1$ has circle distance between $1/3$ and $1/2$. If $d_s=|T_s\mathbin\triangle (T_s+v_s)|$ is measurable and $\bar d=(1/2)\int_0^2 d_s\,ds$, then
$$
    |E|\le U+\bar d/4.
$$
Consequently, attaining the benchmark requires $\bar d>7/1000$ for every such choice. The exact-period case needs just one nontrivial period in the planar torus. A nonzero coordinate of that period generates a cyclic subgroup containing an element of circle distance in $[1/3,1/2]$, or a dense subgroup meeting this interval. In finite order $k\ge2$, use distance $\lfloor k/2\rfloor/k$. Replacing the period by a multiple preserves invariance. A permutation of the coordinates and reversal of the shift give a first-coordinate increment $a\in[1/3,1/2]$. Permutation preserves the chart Haar measure since the induced change of two-coordinate charts has determinant of absolute value one.

**Proof.** For fixed $s,x$ put $q=s-x$. When $x<1/2$, the allowed segment $y+(s-x-y)=q$ uses two unit coordinates with their upper-half square removed. When $x>1/2$, both remaining coordinates lie in the lower half. Measuring in the $y$ parameter gives
$$
 w_s(x)=
 \begin{cases}
  \max(0,\min(q,3-2q)),&x<1/2,\\
  \max(0,\min(q,1-q)),&x>1/2 .
 \end{cases}
$$
These tents also follow by summing the lengths of the two disjoint rectangles with first coordinate low or high. Write $c_s=\int w_s(x)\,dx$ and $J_s(a)=\int\min(w_s(x),w_s(x+a))\,dx$ with arguments reduced modulo one.

Put $K=|C_s\cap T_s|$, $K'=|(C_s-v_s)\cap T_s|$. Equal mass of $T_s$ and its translate implies $|K-K'|\le d_s/2$. After adding the two intersection indicators, the contribution of their union is at most $|T_s|$. The contribution where both are present is at most $J_s(a)$, by bounding the intersection length in each column by the smaller of its two lengths. Thus
$$
  K\le \min\{A,c_s,(A+J_s(a))/2\}+d_s/4 .
$$
If the templates additionally meet every coordinate-root circle in relative measure at most $1/2$ almost everywhere, the same proof uses $w_s\leftarrow\min(w_s,1/2)$ throughout. Indeed each of the two intersections with $T_s$ then occupies at most half the column, as does their overlap. Only the unrestricted version is needed for the theorem.

**Exact finite bound on the entire continuum.** Set $n=1200$, $A_+=304098/10^6>A$. For $s\in[i/n,(i+1)/n$) and (x\in[j/n,$j+1$/n)), (nq\in[i-j-1,i-j+1]). The two tent peaks in these scaled coordinates are (n,n/2). Clamp the corresponding peak to this closed interval and evaluate the scaled tent there to obtain its maximum, an integer (W_j). If (h=\lfloor na\rfloor), the shifted column index can only be (j+h) or (j+h+1) modulo (n). Hence
$$
 c_s\le n^{-2}\sum_j W_j,qquad
 J_s(a)\le n^{-2}\max_{n/3\le h\le n/2}
 \sum_j\min(W_j,\max(W_{j+h},W_{j+h+1})).
$$
Inserting these integer upper bounds into the displayed inequality and summing over the $2n$ slabs with weight $1/(2n)$ gives $U$ exactly. The same sum using the additional circle bound gives $1139714248240000/6912000000000000$. These are explicit upper bounds. Finer meshes can decrease them. The independent standard-library verifier at $n=180$ already gives $152677547/911250000<0.167694$ without the circle condition. The square comparisons in that verifier certify the algebraic threshold and the stated gap.

**Application to pullbacks.** If each template is the inverse image of an area-$A$ planar set under a translated integer torus map of determinant with absolute value greater than one, it inherits a nonzero period from that map's finite kernel. Thus even using a different such map and a different planar set at every sum cannot give the target volume. Area is preserved under pullback by these surjective maps. The theorem applies equally to any measurable subset of the intersection, even if that subset itself has lost the period.

A second consequence concerns large unimodular changes of coordinates of the specific polygon. The original verifier divides it into twelve convex planar cells in a unit square. A coordinate shift of size $h$ changes their union by symmetric difference at most $24|h|$, by slicing each cell into intervals parallel to the shift. Torus projection can only reduce this bound. Let $M$ be unimodular, $L=\max_{ij}|(M^{-1})_{ij}|$, and take the column $j$ attaining $L$. The physical shift $v=M^{-1}e_j/(2L)$ has a coordinate of distance $1/2$; the translated pullback of the polygon changes by at most $12/L$. If on almost every section we use either a template with a nonzero period or such a polygon pullback with $L\ge1715$, then $\bar d\le12/1715<7/1000$ (or use the uniform pointwise bound directly). This also falls below the benchmark. The proof leaves room for less distorted unimodular charts, general aperiodic planar sets, other outer bodies and higher dimensions.

**Reproduction.** The C++17 program uses 64-bit integer arithmetic at the stated meshes. The Python 3 program independently builds the widths from literal rectangular sections. Commands from this folder:

    c++ -std=c++17 -O3 verify.cpp -o verify
    ./verify 1200
    ./verify 1200 circle
    python3 check.py

The complete argument is written here. Its finite sum has two executable checks at distinct resolutions. This note contains no Lean formalization or claim of acceptance of the Erdős problem.
