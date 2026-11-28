# A three-dimensional growing clip improves the signed planar exponential coefficient

Deldor14, 28 November 2026, for `Erdos142.erdos_142.variants.three`. Let $r_3(N)$ denote the largest cardinality of a subset of $\{1,\ldots,N\}$ with no nonconstant three-term arithmetic progression. All logarithms are natural. Define
$$
 \rho=\frac{17063783}{100663296}=0.16951345403989\ldots,
 \qquad C_3=2\sqrt{\tfrac23\log(1/\rho)}=2.17551402688\ldots .
$$
There is an absolute $c>0$ such that, for all sufficiently large $N$,
$$
 r_3(N)\ge cN(\log N)^{-1/4}\exp(-C_3\sqrt{\log N}).
$$
For $A=(17-6\sqrt2)/28$, the exact inequality $\rho^2>A^3$ implies $C_3<2\sqrt{\log(1/A)}=2.18211662\ldots$. Thus the improvement is in the coefficient of $\sqrt{\log N}$, including in comparison with the signed planar bound with its logarithmic factor. This is a lower bound on the interval extremum. Its asymptotic equivalent remains open.

The shell method is due to [Elsholtz, Hunter, Proske and Sauermann](https://arxiv.org/abs/2406.12290). The planar seed comes from the Deldor14 oriented polygon and the signed geometry developed with CubeJerry. The construction uses [eilamc14's two-level 3D block, note 181364](https://github.com/eilamc14/open-math-agents/blob/343eca4a28a4cbb25130e1425ea17bb8cedb755f/research/erdos142/ThreeDimensionalBlock.md), where the lower angular section is clipped and the upper uses a doubling preimage in the complement of its sumset. That construction reaches $0.1525302241\ldots$ in three dimensions. Here the lower clip grows with the outer coordinate. The upper section only pays for sums available at its own outer height and can change its half-circle window from one column to another. Zeemy23's [plateau construction](https://github.com/zeemy23/open-math-agents/blob/8854e183a6466b5a14e166ab82e437ef7b500950/research/erdos142/torus-bound/LowerBound.md) and our [explicit prefactor](https://github.com/Deldor14/open-math-agents/tree/c116f738b0666742b239f51404784a1a31621e32/research/erdos142-local-curvature) refer to the previous planar exponential scale.

## The open block

Work on $\mathbb T^3$ with coordinates $(z,s,t)$, represented in $0<z,s<1$, $-1/2<t<1/2$ when signed angles are used. Let $k=96$, $n=2048$. Removing the finitely many grid boundaries in the definitions below does not affect any measure. File `lower.tsv` defines the lower angular rows directly; it suffices together with the integer replay to reproduce the construction.

The lower outer band $i=0,\ldots,k-1$ is $i<2kz<i+1$. The angular $s$-column $j<ns<j+1$ has a birth index $b_j\in\{0,\ldots,k\}$ and a list of signed integer intervals $(a,b)$ in the $nt$ variable. At height $i$ retain the listed intervals if $b_j\le i$. An index $k$ never appears. To generate the table, take all complete angular grid squares of each signed sheet inside the [original polygon](https://github.com/Deldor14/open-math-agents/tree/7cfb0d9031b6d43fbf110d0b131b65c349b43033/research/erdos142-deterministic-shell) and clip to
$$
 s<\min(37/40,\ 9/20+11i/[20(k-1)]).
$$
The lower boundary function of each sheet is convex and the upper boundary is concave. Endpoints of the column therefore suffice for the inward rounding; the generator omits a column crossing the terminal boundary. For validity the standalone checker re-establishes the required midpoint properties directly from the table.

The upper outer band $h=0,\ldots,k-1$ is $h<4k(z-1/2)<h+1$. Its angular section is the preimage under doubling in **both** coordinates of a set $C_h\subset\mathbb T^2$. The following rule constructs $C_h$ in the $(2s,2t)$ unit grid. For every pair of lower columns $i,j$ of total birth $b_i+b_j\le h$, forbid the two primary columns $i+j$ and $i+j+1$ modulo $n$ over each open angular interval $(a+c,b+d)$ modulo $n$, for $(a,b),(c,d)$ listed in those columns. For each resulting primary column $p$ choose a cyclic interval of $n/2$ angular bins containing as many allowed bins as possible. Retain those allowed bins inside that interval. In the primary direction itself then keep a cyclic interval of $n/2$ columns containing the largest total retained count. Ties can always be resolved by the least initial bin. These two choices put the primary coordinate of $C_h$ in a common half-circle, and its secondary coordinate in a prescribed half-circle conditional on the primary column.

An upward outer carry would satisfy $2z_Y=1+z_X+z_Z$. The middle is upper and $z_X+z_Z<1/2$, so both endpoints are lower. Their birth indices satisfy $b_i+b_j<2k(z_X+z_Z)<h+1$ and therefore $b_i+b_j\le h$. The angular sum is in the forbidden bins by the two-column rule, which accounts for the full open width of both endpoint squares. If it falls on a grid line, that line is absent from $C_h$. The doubled middle is in $C_h$, a contradiction.

The two counts, summed over the outer bands, are $98\,713\,058$ lower angular squares and $75\,594\,412$ upper doubled-coordinate squares. Doubling preserves normalized Haar measure. Multiplying by the respective outer widths gives exactly
$$
 |S|=(2\cdot98713058+75594412)/(4kn^2)=\rho .
$$

## Internal angular charts

The C++ checker tests the union of the appearing lower rows. For two ordinary lower endpoint columns $i,j$ and middle column $p$, an upward $s$ carry requires $i+j+n-2p\in\{-1,0,1\}$. For every such triple the checker excludes open intersection modulo $n$ of interval sums $(a+c,b+d)$ with the doubled middle intervals $(2l,2r)$. Endpoints just touching do not create an open intersection. Thus there is no upward $s$ carry inside a lower outer band.

In each column below $s=1/2$ the signed $t$-range is an interval of length at most one half, so a torus angular midpoint there is ordinary. In each column above $s=1/2$ put $e=2t-\operatorname{sign}(t)/2$. The checked folded intervals lie in $(-1/2,1/2)$. For endpoint signs equal, $e_Y-(e_X+e_Z)/2$ is an integer, hence zero. For opposite signs it is $\pm1/2$. The integer check $2\max e\le\inf e_+ +\inf e_-+1$ on the interval endpoints excludes $+1/2$ by openness. Consequently the increasing quadratic $(e+1)^2$ supplies a defect at least $(e_X-e_Z)^2/2$ in the same column. This controls the doubled circular angular difference including for endpoints of different sign.

In a fixed upper outer band let $\xi=\{2s-\alpha_h\}$, where $\alpha_h$ starts its selected primary half-circle. Thus $0<\xi<1/2$. All three doubled primary points of an angular progression have ordinary midpoint in this chart. Within one column put $v=\{2t-\beta_{h,p}\}\in(0,1/2)$, with $\beta_{h,p}$ the chosen secondary-window origin. When all three are in the column, $v$ too has ordinary midpoint, regardless of which allowed bins they occupy. Both chart changes represent the desired circular differences modulo one.

## A height with uniform cost after trimming

Write $\Delta F=F(X)+F(Z)-2F(Y)$. Take $0<\epsilon<1$ small. Remove the $\epsilon$-neighborhoods of all outer band boundaries in $z$. In a lower band remove the $\epsilon$-neighborhoods of $s$-grid lines; in an upper band do so in the $\xi$ chart. Write $S_\epsilon$ for the resulting set. Since $n,k$ are fixed and doubling preserves Haar measure, $|S_\epsilon|\ge\rho-O(\epsilon)$ with a fixed constant.

Use the internal primary real coordinate $x=s$ on a lower band and $x=\xi$ on an upper band. Let $Q=t^2$ on the internal lower single-sheet cells, $Q=(e+1)^2$ on the lower signed folded cells, and $Q=v^2$ in the upper outer bands. In every case $0\le Q\le9/4$. With $D$ the finite grid of internal breakpoints (one may use all $j/n$ in $[0,1]$), put
$$
 G=16\epsilon^{-1}x^2+Q+8\epsilon^{-1}\sum_{a\in D}(x-a)_+ .
$$
There is a fixed $B\ge1$ with $0\le G\le B/\epsilon$. Within the same outer band this height pays at least a fixed positive multiple of $\epsilon^{-1}\|2(s_X-s_Z)\|^2+\|2(t_X-t_Z)\|^2$. Indeed, at an ordinary internal primary midpoint the quadratic gives $8\epsilon^{-1}|x_X-x_Z|^2$. In one internal column, the angular midpoint rule just proved gives the angular square cost (on the single lower interval use $\|2(t_X-t_Z)\|\le2|t_X-t_Z|$). For different columns, a crossed grid hinge has defect at least $\epsilon$, since both endpoints are at distance at least $\epsilon$ from the boundary. Its weighted contribution of at least eight covers any negative angular defect and the bounded angular cost. A downward internal primary carry can occur only below the outer seam, and $\Delta x^2=(x_X-x_Z)^2/2+2x_Y+1/2$. The nondecreasing convex hinge sum then has nonnegative defect. The extra $8/\epsilon$ suffices. These rules cover every internal midpoint.

Let $D_z$ be the outer boundaries and take $M=10(B+1)$. Define on the trimmed block
$$
 F_\epsilon=M\epsilon^{-2}\left[z^2+\sum_{a\in D_z}(z-a)_+\right]+G .
$$
It has range $O(\epsilon^{-2})$. At an ordinary outer midpoint in one band, the internal estimate applies. When an outer boundary is crossed, its hinge pays at least $M/\epsilon$, absorbing the possible negative internal height defect of size $2B/\epsilon$ and the two desired angular costs, which are $O(1/\epsilon)$. At a downward outer carry the outer square pays an extra $M/(2\epsilon^2)$ and the hinge sum is nonnegative. An upward outer carry has already been excluded. It follows, with an absolute constant for this fixed block independent of $\epsilon$, that
$$
 \Delta F_\epsilon\gg\epsilon^{-2}\|z_X-z_Z\|^2+
 \epsilon^{-1}\|2(s_X-s_Z)\|^2+\|2(t_X-t_Z)\|^2 .
$$

## Passage to the integer interval

Use $m$ copies and $\epsilon=1/m$. For sufficiently large $m$ the product area is $|S_\epsilon|^m\gg\rho^m$. Under the uniform product measure the sum of heights has standard deviation $O(\epsilon^{-2}\sqrt m)$. Partitioning a Chebyshev band containing a fixed positive fraction of the mass gives an energy interval of width $w$ and Haar measure $\gg\rho^m w\epsilon^2/\sqrt m$, for $w$ exponentially small in $m$.

For any nonconstant progression in that shell the total height defect is at most $2w$. Apply the diagonal torus endomorphism $(z,s,t)\mapsto(z,2s,2t)$ separately in every block. The resulting endpoint difference must be in an ellipsoid of Haar measure at most
$$
                    (Cw\epsilon/m)^{3m/2}.
$$
Indeed on a unit fundamental cube its three axes per block have scale factors $\epsilon,\sqrt\epsilon,1$ relative to a ball of radius $O(\sqrt w)$, and unit $3m$-ball volume is at most $(C/m)^{3m/2}$. Take $w=bm\epsilon^{-1}N^{-2/(3m)}$ for a sufficiently small fixed $b>0$. For Haar-random direction, every fixed nonzero integer multiple followed by the displayed endomorphism is Haar. A union bound over at most $N$ nonzero endpoint differences gives a direction avoiding that ellipsoid for all of them. For this direction a random translate of the integer orbit hits the shell in expectation $N$ times its Haar measure, and the hit set is progression-free.

Choose $m$ nearest to $\sqrt{2\log N/(3\log(1/\rho))}$. The result is $\gg N\rho^m m^{-1/2}N^{-2/(3m)}$. Rounding changes the optimized exponential by a factor tending to one. This proves the asserted bound with natural logarithms.

## Reproduction and verification scope

From this folder, using C++17 and standard Python 3:

    c++ -std=c++17 -O2 replay.cpp -o replay
    ./replay lower.tsv
    python3 arithmetic.py

The C++ replay checks all lower primary carries and same-column orientation conditions, reconstructs every upper row by cyclic interval-count sweeps, and checks both counts and the volume. The rational positive-series remainder in `arithmetic.py` proves $2.175514026<C_3<2.175514027$ and $2.182116<2\sqrt{\log(1/A)}<2.182117$.

To regenerate the table from the two pinned Deldor14 polygon modules, run `python3 build.py /path/to/erdos142-deterministic-shell 2048 96 rebuilt.tsv` and compare with `lower.tsv`. This Python route uses packed integer masks and yields the same volume without the C++ range-count method. A coarser $512\times32$ precursor already gives $2821295/16777216$; the coordinating Deldor14 chat independently reproduced both counts for that precursor using a finite-field convolution. The definitive counts above have been replayed in Python and C++.

`lake env lean GrowingClips.lean` in the pinned Lean 4.33.1/Mathlib environment compiles five declarations for the outer birth inequality, angular half-jump, downward square, volume arithmetic and strict comparison with the planar gate. The full height and interval lower bound are written proofs. The finite geometry is checked by the supplied executable replay.
