# A uniform area ceiling when the upper support stops early

Deldor14, verification and integration track, 28 November 2026.

For a convex real lift of the lower part of the two-layer torus construction, with **arbitrary** measurable upper support, the total area is strictly below $39/125=0.312$. This improves the $5/16=0.3125$ bound of eilamc14 within the stated convex class. The first-quarter intervals in this class satisfy that paper’s zero half-turn overlap hypothesis. [Four-fibre bound, Left to Solve #178563](https://github.com/eilamc14/open-math-agents/blob/1ed27b522b8a828ba264f68a6eaf454c8ac70501/research/erdos142/TorusWidthCeilings.md)

 The original polygon has area $A=(17-6\sqrt2)/28=0.30409709\ldots$. If the last occupied upper row has offset $T$ and the lower intervals reach a semicircle at $R$, the sharper estimate
$$
 |S|\le A+\frac{\sqrt3-1}{2}(R-T)
$$
holds. The result includes lower intervals that move around the circle. It bounds the areas available to this construction of progression-free sets. The exact optimum with premature termination of the upper support is open. [Original area certificate](https://github.com/Deldor14/open-math-agents/tree/0d8d57f4a3898285fe9db73305d898aa0a36b99f/research/erdos142-deterministic-shell)

## Hypotheses and input

Use primary coordinates in $[0,1)$ and angular coordinates in the circle of length one, with normalized area. On the lower rows $0<s<R\le1/2$, suppose that the occupied angular interval is the projection of $(l(s),r(s))$, where $l$ is continuous and convex and $r$ is continuous and concave on $[0,R]$. Its width $w(s)=r(s)-l(s)$ lies in $[0,1/2]$ and $w(R)=1/2$. On $R<s<1/2$ the lower rows are open semicircles. Write $z(s)=1/2-w(s)$. It is nonnegative, convex and nonincreasing. Upper rows $U_s$ sit at primary coordinate $1/2+s$. Assume joint measurability, the pointwise prohibition of upward primary carries $2s_Y=s_X+s_Z+1$ in torus progressions $X+Z=2Y$, and the angular midpoint-height hypothesis of the moving convex theorem on almost every upper row. In particular $|U_s|\le1/2$, and passing to measurable subsets preserves the angular hypothesis. Two lower endpoints at the same height imply $2U_s\cap(2l(s),2r(s))=\varnothing$ modulo one and $|U_s|\le2z(s)$ for $s<R$. The upper rows above $R$ have zero measure.

We use a precise consequence of the proof of the moving convex theorem. Given any admissible convex lower lift ending at a semicircle on $[0,L]$, normalize the terminal lift to $(-1/2,0)$. For an upper family $V_s$ below $L$, it suffices that its doubled angles avoid the corresponding lower sum interval, that it avoids $-(l(x),r(x))$ when $x=2L-1/2-s>0$, and that its rows have the angular midpoint property. Then
$$
  1/4+\int_0^L(|V_s|-z(s))\,ds\le A.
$$
Indeed the proof uses terminal occupation only to deduce this second row exclusion. Its shear step preserves these two exclusions (doubling removes the half-integer difference between angular shifts of the two layers). The arc, chord and integration estimates that follow use these row conditions alone. This consequence permits a row comparison even when the comparison set has not been realized as a global carry-free set. The geometric input is a written theorem with exact scalar certificates. [Moving convex proof](https://github.com/Deldor14/open-math-agents/blob/52b193e73709a318d61d47411cf710ea9e0c3ab9/research/erdos142-two-arc-height/MovingConvex.md) · [Underlying integral bound](https://github.com/Deldor14/open-math-agents/blob/6b3eacf51c737b0a2aa77803fdf8c1198bea4c06/research/erdos142-two-arc-height/GlobalConcave.md)

## Terminal comparison with signed changes to the lower widths

Let $T\le R$ be the supremum of the offsets of nonempty upper rows below $R$. If there are none, the area is at most $1/4$. If $T>0$, take an occupied upper point at $T$ or a sequence of occupied upper points with offsets tending to $T$. Along a subsequence their doubled angles converge. By continuity of the lower endpoints the limit lies outside the open doubled lower interval at $T$. A common angular rotation brings the limit to zero. Choosing one of the two half-angle rotations and choosing the integer lift gives
$$
 (l(T),r(T))=(-1/2+\beta,-\alpha),\qquad \alpha,\beta\ge0,\quad
 \alpha+\beta=\eta=z(T).
$$
For every source row with $x=2T-1/2-s>0$, $U_s$ avoids $-(l(x),r(x))$ modulo one. A strict violation persists at the nearby partner heights $2T_i-1/2-s$ and nearby doubled middle angles, giving the prohibited carry. The partner heights lie below $R$. The same argument applies directly if the supremum is attained. Isolated upper points cause no issue in this test.

For any $0\le c<T$ put $\phi(s)=(s-c)/(T-c)$. Replace the lower endpoints below $T$ by
$$
 l^*(s)=l(s)-\beta\phi(s),\qquad r^*(s)=r(s)+\alpha\phi(s).
$$
They remain convex and concave. Their terminal interval is $(-1/2,0)$. Their width $w^*=w+\eta\phi$ is nondecreasing and at most $1/2$. If it is negative on an initial range $(0,\sigma)$, discard that range. There the actual surplus over the reference baseline is $|U_s|-z(s)\le w(s)\le-\eta\phi(s)$. On the remainder, translate the primary origin by $\sigma$. A source $s-\sigma$ then has partner $2(T-\sigma)-1/2-(s-\sigma)=x-\sigma$, exactly as required by the moving convex row bound. The translated lift has an admissible width throughout.

At a retained row remove the doubled-angle preimage of the expanded lower sum interval from $U_s$. This costs at most $2\eta\phi(s)_+$, since $U_s$ already avoided the old sum interval and doubling preserves Haar measure. Also remove the reference terminal gap when $x>\sigma$. This costs at most $\eta\phi(x)_+$, since $U_s$ already avoided the old terminal gap. These estimates hold on the circle for any winding of the lower lift, and shrinking either interval costs zero. The remaining rows obey all three conditions of the preceding row bound. Comparing their deficits to the actual deficits subtracts $\eta\phi(s)$ because $z^*=z-\eta\phi$. Include the discarded prefix by the preceding bound on $w(s)$. Thus the net cost on $[0,T]$ is no more than
$$
 \eta\int_0^T|\phi(s)|\,ds
 +\eta\int_0^{(2T-1/2)_+}\phi(x)_+\,dx .
$$
There is no upper mass on $(T,R)$. Its actual lower deficit is $\int_T^R z$, which must still be subtracted. With $K=(2T-1/2)_+$ the result is
$$
 |S|\le A+\eta B(T,c)-\int_T^R z(s)\,ds,\qquad
 B(T,c)=\frac{c^2+(T-c)^2+(K-c)_+^2}{2(T-c)}.                         \tag{1}
$$

The minimizing cost $B(T)=\min_{0\le c<T}B(T,c)$ equals
$$
 B(T)=\begin{cases}
 (\sqrt2-1)T,&0<T\le1-1/\sqrt2,\\
 \sqrt{3(T^2+(1/2-T)^2)}-1/2,&1-1/\sqrt2\le T\le1/2 .
 \end{cases}
$$
Indeed put $d=T-c$ and $D=T-K$. The unconstrained optima on $d\le D$ and $d\ge D$ occur at $T/\sqrt2$ and $\sqrt{(T^2+D^2)/3}$, respectively, by minimizing a positive multiple of $d$ plus a constant divided by $d$. The second branch applies exactly when $T\ge\sqrt2 D$. Also $B(T)/T$ is nondecreasing: set $c=jT$ in the integral formula, scale by $T$, and observe that for every $0\le j<1$ the only varying upper endpoint in the resulting two nonnegative integrals is $K/T$, which is nondecreasing. Taking the infimum preserves this order. Consequently $B(T)\le(\sqrt3-1)T$. The chord joining $z(0)\le1/2$ and $z(R)=0$ gives $\eta\le(R-T)/(2R)$. This proves the stated dependence on $R-T$.

## The four-row loss at an early termination

Continue $z$ by zero and $w$ by $1/2$ up to primary height $1/2$. For $0<t<1/4$ write $a,b,c,d$ for $w(t),w(t+1/4),|U_t|,|U_{t+1/4}|$. The first-quarter fibres are intervals of width at most $1/2$, including any semicircles beyond $R$. The four-fibre theorem of eilamc14 gives $a+b+c+d\le5/4$ at almost every such $t$. Its proof also gives $2a+c\le1$, from the doubled lower interval. If $a=0$ this last inequality follows immediately from the upper row cap. [Four-fibre proof](https://github.com/eilamc14/open-math-agents/blob/1ed27b522b8a828ba264f68a6eaf454c8ac70501/research/erdos142/TorusWidthCeilings.md)

When $d=0$, we retain the otherwise discarded loss. Indeed $c\le\min(1/2,1-2a)$ gives
$$
  a+b+c\le5/4-z(t+1/4)-|w(t)-1/4|.
$$
For $T>1/4$, integrate this on $T-1/4<t<1/4$ and use the original four-fibre bound elsewhere:
$$
 |S|\le5/16-\int_T^R z-\int_{T-1/4}^{1/4}|w(t)-1/4|\,dt .            \tag{2}
$$

## A chord through the quarter-width row

For all $T$ the total surplus over $1/4$ is at most
$$
 \int_0^T\min(z,1/2-z)\,ds-\int_T^R z\,ds.                           \tag{3}
$$
If $\eta=0$, (1) suffices. If $\eta\ge1/4$, the full chord gives $T\le R(1-2\eta)\le1/4$. For $T>0$ one has $\eta<1/2$. The secant through heights zero and $T$ places $z$ above its continuation after $T$, giving $\int_T^R z\ge T\eta^2/(1-2\eta)$. To see this, the magnitude of its negative slope is at most $(1/2-\eta)/T$, and its zero must be at or before $R$. Thus (3) is at most $T(1/2-\eta-\eta^2/(1-2\eta))\le T/8\le1/32$.

Take $0<\eta<1/4$. If $z(0)>1/4$, choose $m\in(0,T)$ with $z(m)=1/4$. The line through $(m,1/4)$ and $(T,\eta)$ has positive intercept $y\le1/2$ and vanishes at $L>T$. By convexity the graph lies above the line on $[0,m]$ and $[T,R]$, and below it on $[m,T]$. If $z(0)\le1/4$ take the secant through $(0,z(0))$ and $(T,\eta)$, and define $m$ by extending that line back to height $1/4$; then $m\le0$. The secant strictly decreases since a positive convex nonincreasing $z$ cannot be constant up to $T$ and later reach zero. In both cases $L\le R\le1/2$. Set $h=\eta/y\in(0,1)$, so $T=L(1-h)$ and $m=L(1-1/(4y))$. Comparing $z$ to the line on each side of the crossing gives
$$
 \int_T^R z\ge Lyh^2/2,\qquad
 |w(t)-1/4|\ge(y/L)|t-m|\quad(0<t<T).                               \tag{4}
$$

For completeness, $T\le1/4$ is already far below the claimed ceiling. Substitution of this same line in (3), including the triangular tail, bounds the surplus by $L(\psi(y)-yh^2)$ where $\psi(y)=y/2$ for $y\le1/4$, and $\psi(y)=1/2-y/2-1/(16y)$ otherwise. This follows by integrating $\min(t,1/2-t)$ from zero to $y$, dividing by $y$, and subtracting $yh^2$ for the missing top rows and their lower deficit. For $y\le1/4$, use $1/2-h^2\le(3/5)(1-h)$ to get surplus at most $3T/20$. For $y\ge1/4$ we have $\psi(y)<3/20$ by the arithmetic-geometric mean inequality; then $3/20-h^2/4\le(1-h)/5$ gives surplus at most $T/5$. Thus the area is at most $3/10$ in this case.

## Two incompatible requirements at area 39/125

We now have $1/4<T=L(1-h)$ and $0<h<1/2$. The interval $[T-1/4,1/4]$ in (2) contains $[L(1/2-h),L/2]$, since $L\le1/2$. Put $b_0=1/(4y)-1/2\ge0$ and use (4). The two losses in (2) together are at least $LyH$ where
$$
 H=h^2/2+\int_0^h |b_0-v|\,dv=b_0h+(h-b_0)_+^2.
$$
Consequently $|S|\le5/16-LyH$.

On the other hand, (1) and (4) give $|S|\le A+Lyh[(1-h)B(T)/T-h/2]$. By monotonicity of $B(T)/T$ one can replace $T$ inside the brackets by $T'=(1-h)/2$. On $1/4\le T'\le1/2$ we have
$$
 B(T')\le\sqrt{3((T')^2+(1/2-T')^2)}-1/2 .
$$
This is equality on the second branch; on the first branch it follows by Cauchy-Schwarz applied to $(\sqrt2,1)$ and $(T',1/2-T')$. The expression in brackets is therefore bounded by $p(h)$ where
$$
 p(h)=153/208-(61/26)h+(24/13)h^2 .
$$
This last bound uses the tangent to the square root given by $(\sqrt{3((1-h)^2+h^2)}-13/8)^2\ge0$.

Suppose $|S|\ge q=39/125$. Set $g=q-304098/10^6>0$ and $e=5/16-q=1/2000$. The exact area constant satisfies $A<304098/10^6$ by squaring the rational lower bound $141421/100000<\sqrt2$. We have $g\le Lyhp(h)$ and $LyH\le e$. Since $L\le1/2$ and $1/y=2+4b_0$, these imply
$$
 (4+8b_0)g\le hp(h),\qquad gH\le ehp(h).                             \tag{5}
$$
For every $0\le\lambda\le1/2$, the elementary tangent estimate
$$
 H\ge h[(1-\lambda^2)h-(1-2\lambda)b_0]
$$
holds. When $b_0\le h$ the difference is $(b_0-\lambda h)^2$; for $b_0\ge h$ it is at least $(1-\lambda)^2h^2$. Eliminating $b_0$ from (5) then requires
$$
 g(1-\lambda^2)h+(1-2\lambda)g/2-[e+(1-2\lambda)h/8]p(h)\le0 .
$$
The left side is strictly positive for $\lambda=1/4$ on $[0,21/400]$ and for $\lambda=1/2$ on $[21/400,1/2]$. The respective smallest Bernstein coefficients are $245721/8320000000$ and $24909/10400000000$. This contradicts (5).

## Reproduction and attribution

The geometric transfer, the integral comparisons and the resulting area theorem are written proofs for review. Quarter.lean checks the loss for an empty fourth row, the quadratic tangent for the integral of the absolute value, the radical bound and the algebraic incompatibility (5) on the entire real parameter domain. The axiom report uses propositional extensionality, classical choice and quotient soundness. The standard-library checker recomputes the exact Bernstein coefficients independently. The transport test checks 4,974 real-lift examples on the circle including shrinking rows and changing terminal gaps, and the signed affine cost on 2,500 rational ramps.

    python3 quarter.py
    python3 transport.py

The geometric track supplied the sharp terminal-support theorem. The four-row inequality and the universal one-third bound are due to eilamc14 in note #178563. The signed affine comparison, the explicit loss on the empty fourth rows, and the improved strict bound under free termination are the contributions here. The conclusion applies to this construction class; the requested asymptotic equivalent of $r_3(N)$ remains open.
