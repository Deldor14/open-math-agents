# A sharp obstruction for abstract deficit separation

All logarithms have base two. Fix constants $c>0$, $C_0\ge0$, and $C_1\ge0$ with $c+C_0>1$. There is a nondecreasing subadditive integer function $e$ on the nonnegative integers with $e(0)=1$, successive increments in $\{0,1\}$, and
$$
\frac{t^{1/6}}{\log(2+t)}\ll e(t)\ll 1+\sqrt t .
$$
For $y\ge1$ put $T(y)=\max\{t:e(t)\le y\}$. Every sequence of nonnegative integers $(u_i)_{i\ge1}$ satisfying
$$
u_{j+h}-u_j\ge T(c(h+1)+C_0)+C_1\qquad(j,h\ge1)
$$
has infinitely many indices $i$ at which
$$
e(u_i)-ci\gg i^{4/5}\bigl(\log(2+i)\bigr)^{6/5}.
$$
Consequently the power and logarithm in this separation method’s upper estimate are both necessary for the abstract class. The conclusion concerns this criterion for abstract deficits. Whether the deficit of the true Roth number has the same behavior remains open.

## Construction

For every integer weight $r\ge1$ allow an ordinary coin of value $r^2$, with unlimited copies. Choose increasing integers $h_k$ and set
$$
w_k=\lfloor c(h_k+1)+C_0\rfloor,\quad
L_k=\lceil\log(2+w_k)\rceil,\quad
V_k=w_k^6L_k^6,\quad m_k=V_k/w_k^2=w_k^4L_k^6 .
$$
Allow one special coin type of weight $w_k$ and value $V_k$ for each $k$, again with unlimited copies. Choose $w_1\ge2$ and each $h_{k+1}$ large enough that $w_{k+1}>m_k w_k$. Define $F(n)$ to be the largest value attainable with total weight at most the integer $n$.

Concatenation shows that $F$ is superadditive. An ordinary coin of weight one makes $F$ strictly increasing. For $n\ge1$ one has
$$
n^2\le F(n)\le n^6\lceil\log(2+n)\rceil^6 .
$$
The lower bound uses one ordinary coin. For the upper bound every available coin of weight $r\le n$ has value at most $r\,n^5\lceil\log(2+n)\rceil^6$. Put $e(0)=1$ and $e(t)=\min\{n:F(n)\ge t\}$ for $t\ge1$. Superadditivity and strict increase give the stated subadditivity and unit increments of $e$. The displayed bounds on $F$ give the growth bounds on $e$, and $T(y)=F(\lfloor y\rfloor)$ for $y\ge1$. In particular $T$ is superadditive on its domain and $e(T(y))=\lfloor y\rfloor$.

## Forced excess

Fix $k$ and abbreviate its data by $h,w,L,V,m$. At any integer budget $y<mw$ the available coins all have value per unit weight at most $V/w=w^5L^6=mw$. For an ordinary coin its value per unit weight is its weight $r\le y$. For special coins the ratios $V_k/w_k$ increase with $w_k$, and every later special coin exceeds the budget. Thus $F(y)\le yV/w<mV$, while $m$ copies of the current special coin attain $mV$ at weight $mw$. It follows that $e(mV)=mw$.

Iterate the separation inequality $m$ times with step $h$, starting at $j=1$. Since $T(c(h+1)+C_0)=F(w)\ge V$, at $i=1+mh$ one has $u_i\ge mV$ and
$$
e(u_i)-ci\ge m(w-ch)-c\ge m(c+C_0-1)-c.
$$
Finally $h\asymp w$, so $i\asymp w^5L^6$ and $\log(2+i)\asymp L$. Therefore $m=w^4L^6\asymp i^{4/5}(\log(2+i))^{6/5}$, as claimed.

If only a pure-power example is desired, taking $L_k=1$ throughout gives $T(y)\le y^6$ and the lower bound $\gg i^{4/5}$.
