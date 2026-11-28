# A sharp obstruction for abstract deficit separation

All logarithms have base two. Fix constants $c>0$, $C_0\ge0$, and $C_1\ge0$ with $c+C_0>1$. There is a nondecreasing subadditive integer function $e$ on the nonnegative integers with $e(0)=1$, successive increments in $\{0,1\}$, and
$$
\frac{t^{1/6}}{(\log(2+t))^{1/6}}\ll e(t)\ll 1+\sqrt t .
$$
For $y\ge1$ put $T(y)=\max\{t:e(t)\le y\}$. Every sequence of nonnegative integers $(u_i)_{i\ge1}$ satisfying
$$
u_{j+h}-u_j\ge T(c(h+1)+C_0)+C_1\qquad(j,h\ge1)
$$
has infinitely many indices $i$ at which
$$
e(u_i)-ci\gg i^{4/5}\bigl(\log(2+i)\bigr)^{1/5}.
$$
Consequently the power and logarithm in this separation method’s upper estimate are both necessary for the abstract class. The conclusion concerns this criterion for abstract deficits. Whether the deficit of the true Roth number has the same behavior remains open.

## Construction

For every integer weight $r\ge1$ allow an ordinary coin of value $r^2$, with unlimited copies. Choose increasing integers $h_k$ and set
$$
w_k=\lfloor c(h_k+1)+C_0\rfloor,\quad
L_k=\lceil\log(2+w_k)\rceil,\quad
V_k=w_k^6L_k,\quad m_k=V_k/w_k^2=w_k^4L_k .
$$
Allow one special coin type of weight $w_k$ and value $V_k$ for each $k$, again with unlimited copies. Choose $w_1\ge2$ and each $h_{k+1}$ large enough that $w_{k+1}>m_k w_k$. Define $F(n)$ to be the largest value attainable with total weight at most the integer $n$.

Concatenation shows that $F$ is superadditive. An ordinary coin of weight one makes $F$ strictly increasing. For $n\ge1$ one has
$$
n^2\le F(n)\le n^6\lceil\log(2+n)\rceil .
$$
The lower bound uses one ordinary coin. For the upper bound every available coin of weight $r\le n$ has value at most $r\,n^5\lceil\log(2+n)\rceil$. Put $e(0)=1$ and $e(t)=\min\{n:F(n)\ge t\}$ for $t\ge1$. Superadditivity and strict increase give the stated subadditivity and unit increments of $e$. The displayed bounds on $F$ give the growth bounds on $e$, and $T(y)=F(\lfloor y\rfloor)$ for $y\ge1$. In particular $T$ is superadditive on its domain and $e(T(y))=\lfloor y\rfloor$.

## Forced excess

Fix $k$ and abbreviate its data by $h,w,L,V,m$. At any integer budget $y<mw$ the available coins all have value per unit weight at most $V/w=w^5L=mw$. For an ordinary coin its value per unit weight is its weight $r\le y$. For special coins the ratios $V_k/w_k$ increase with $w_k$, and every later special coin exceeds the budget. Thus $F(y)\le yV/w<mV$, while $m$ copies of the current special coin attain $mV$ at weight $mw$. It follows that $e(mV)=mw$.

Iterate the separation inequality $m$ times with step $h$, starting at $j=1$. Since $T(c(h+1)+C_0)=F(w)\ge V$, at $i=1+mh$ one has $u_i\ge mV$ and
$$
e(u_i)-ci\ge m(w-ch)-c\ge m(c+C_0-1)-c.
$$
Finally $h\asymp w$, so $i\asymp w^5L$ and $\log(2+i)\asymp L$. Therefore $m=w^4L\asymp i^{4/5}(\log(2+i))^{1/5}$, as claimed.

If only a pure-power example is desired, taking $L_k=1$ throughout gives $T(y)\le y^6$ and the lower bound $\gg i^{4/5}$.

## Two-sided power estimates

For every fixed 0<α<1 there is also an abstract deficit e(t) comparable to t^α at all t≥1 for which every such schedule has e(uᵢ)−ci bounded below by a positive multiple of log i at infinitely many i. Here take any C₀>0. This matches the conditional logarithmic upper bound for the composition schedule.

Set vₖ=⌊2^(k/α)⌋ and F(n)=Σ εₖvₖ, where εₖ are the binary digits of n. We have v₀=1 and vₖ₊₁≥2vₖ. Binary carries therefore cannot lower the total value, so F is superadditive. It is strictly increasing since the new high bit when adding one outweighs the erased lower bits. For 2ᴷ≤n<2ᴷ⁺¹ one has v_K ≤ F(n) < 2v_K. Thus F(n) is comparable to n^(1/α). Define e as the maximum of 1 and the least integer y with F(y)≥t. It is nondecreasing and subadditive with increments zero or one, e(t) is comparable to t^α for t≥1, and T(y)=F(⌊y⌋) for y≥1.

Fix 0<δ≤C₀. For all sufficiently large k let hₖ=⌊(2ᵏ−δ)/c⌋, so c hₖ+δ≤2ᵏ≤c(hₖ+1)+C₀. Starting at index one, use each separation hₖ once for k₀≤k≤K. At i=1+Σhₖ we have uᵢ≥ΣF(2ᵏ)=F(Σ2ᵏ), since the bits are distinct. Hence e(uᵢ)−ci≥δ(K−k₀+1)−c, and i is comparable to 2ᴷ. The kernel checks the carry, strict growth of the weighted binary value, the no-carry equality for distinct bits and the lower bound in terms of their number. [Lean certificate](DeficitPowerSharpness.lean)
