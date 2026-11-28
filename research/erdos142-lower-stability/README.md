# Area stability under measurable edits of the lower layer

Deldor14, verification and integration track, 28 November 2026.

The extremal polygon has a band of lower rows on which deleting any measurable set of area $H$ reduces the largest attainable total area by exactly $H$. This includes deleting the entire band. Lower rows outside that band admit a quantitative perturbation estimate. The estimate concerns the torus construction used for three-term progression-free sets.

## Setting and statement

Use primary representatives $s\in[0,1)$ and physical angles in $\mathbb R/\mathbb Z$, with normalized Haar measure. Write $L_s$ for the actual lower row at $s$, and $U_u$ for the upper row at $1/2+u$, with $0<s,u<1/2$. Assume joint Lebesgue measurability and forbid pointwise every torus progression $X+Z=2Y$ with upward primary carry $2s_Y=s_X+s_Z+1$. In almost every upper row $0<u<V$ assume the bounded-above height condition of the robust row theorem. More explicitly, for each occupied middle $y$, outside a set of endpoints of measure at most $e(u)$, the second difference of the height on occupied triples $(t,y,2y-t)$ is at least $c(u)\|4(t-y)\|^2-\epsilon(u)$, where $c(u)>0$ and $\epsilon(u)\ge0$. Put $\omega(u)=\sqrt{\epsilon(u)/c(u)}+e(u)/2$ and assume it is integrable. The exact angular condition has $e=\epsilon=0$. Use any interval endpoint convention consistently up to the measure-zero boundaries of the *reference* polygon. [Robust angular row theorem](https://github.com/Deldor14/open-math-agents/blob/0ceac02dcb582c84247e32eb8eda54c488cc60e6/research/erdos142-two-arc-height/RobustReflection.lean)

Define the reference intervals and constants by
$$
q=3\sqrt2/4,\quad R=2(1+\sqrt2/3)/7,\quad a=q(1-R),\quad b=qR,
\qquad r(s)=as,\quad l(s)=1/2-b+bs,
$$
$$
L^0_s=(-\min(l(s),1/2-r(s)),r(s)),\quad
G=R/2,\quad V=(3-4\sqrt2/3)/7,\quad F=(3R-1)/2,\quad J=2F-V.
$$
Set $h(s)=|L^0_s\setminus L_s|$, $p(s)=|L_s\setminus L^0_s|$, and $P=\int_0^{1/2}p$. The area of the original polygon is $A=(17-6\sqrt2)/28$. The following estimate holds for arbitrary measurable changes in the lower rows and arbitrary upper support:
$$
 |S|\ \le\ A+P+\int_0^{1/2}w(s)h(s)\,ds+\int_0^V\omega(u)\,du .
$$

| Range of $s$ | $(0,J/2)$ | $(J/2,J)$ | $(J,V)$ | $(V,1/2)$ |
|---|---:|---:|---:|---:|
| $w(s)$ | 2 | 3 | −1 | 1 |

In particular $|S|\le A+P+3\int h+\int\omega$. With exact row costs, changing the lower rows only on $J<s<V$ keeps the optimal **upper** area bounded by the original upper area, even for arbitrary replacement rows there. If the prescribed change simply deletes area $H$ there, the optimum total area is exactly $A-H$. The original upper rows attain it, since deleting lower points preserves the carry condition. Sharpness is asserted for this consequence. The positive coefficients in the table are bounds.

## Localizing upper rows after lower deletions

Let $K_s=L_s\cap L^0_s$ and $\lambda(s)=|L^0_s|$. The latter is at most $1/2$ and at least $\lambda_0=1/2-qR$. Let $E_s$ be the complement of the doubled-angle preimage of the reference sum arc $L^0_s+L^0_s$, and put $T_s=U_s\cap E_s$. Then
$$
 |U_s\setminus E_s|\le 2h(s).
$$
Indeed, for any nonempty compact $K'\subset K_s$ with minimal and maximal real representatives $m,M$ in the lower interval's lift, $m+K'$ and $M+K'$ lie in its sum arc. They meet at most at $m+M$, and have total measure $2|K'|$. The arc projects injectively up to endpoints. All their angles are forbidden for $2U_s$ by the primary carry. Doubling preserves normalized Haar measure. Inner approximation gives the bound, including when $|K_s|=0$. The proof needs no measurability of the unrestricted sum of two measurable sets. For $u<R$, $E_u$ is the double-angle preimage of $I_u=[2r(u),1-2l(u)]$, of length $2q(R-u)$. For $u\ge R$, it has measure zero.

## Pairing rows without using the central lower band

Use the two capped lobes $E^0_u\subset E_u$ defined by truncating the positive magnitudes at $C=\min(1/2-l(u),a(1/2+u))$ and the negative magnitudes at $D=\min(1/2-r(u),l(u)+b/2)$. Write $W(u)$ for the original upper width, zero above $R$. Before $R$ its formula is $2q(R-u)-g-v-\max(f,v)$, where $f=q(F-u)_+$, $g=q(G-u)_+$ and $v=q(V-u)_+/2$. The available overflow lengths are $f$ and $g$. On $(0,J)$ the capped reflection estimate gives $|T_u\cap E^0_u|\le W(u)+\omega(u)$. On $(J,V)$ it gives the direct whole-circle bound $|U_u|\le1/2+\omega(u)=W(u)+\omega(u)$. On $(V,G)$ the capped envelope itself has width $W(u)$, and on $(G,R)$ the full envelope has width $W(u)$. These are the capped-row and whole-circle results established in the preceding work. [Fixed-lower proof and definitions](https://github.com/Deldor14/open-math-agents/blob/2b6d816e7c6f2ffce0a98c97cbe074ed0745e485/research/erdos142-two-arc-height/FreeSupport.md)

Put $\delta=(F-J)/2=1/4-\sqrt2/6$. Choose the upper target $v$ and the lower endpoint row $x=2v-1/2-u$ as follows.

| Upper source $u$ | Target $v$ | Image of $x$ |
|---|---|---|
| $(0,J)$ | $u+1/4$ | $(0,J)$ |
| $(V,G)$ | $u+G-\delta$ | $(J/2,J)$ |

Both target maps and both lower-row maps have slope one. The two target intervals are disjoint inside $(G,R)$ since $1/4+J<V+G-\delta$ and $2G-\delta<R$. In either source band $0<x<R$, so $L^0_x=(-l(x),r(x))$.

First suppose $|K_x|>0$. Take actual lower angles within $\eta>0$ of its essential supremum and infimum in this lift, from within the essential range. Their respective gaps $d_+,d_-$ from the two reference endpoints sum to at most $h(x)+2\eta$, since the two gaps outside the essential range are disjoint and empty almost everywhere in $K_x$. Let $S_+,S_-$ be the positive and negative overflow magnitudes in $T_u$ beyond the caps. The ideal translates $S_++r(x)$ and $1-S_--l(x)$ lie in the leftmost $f$ and rightmost $g$ portions of $I_v$, respectively, by the identities
$$
 a(1/2+u)+r(x)=2r(v),\qquad
 1-(l(u)+b/2)-l(x)=1-2l(v).
$$
The portions have disjoint interiors. On the first band $|I_v|=f+g$. On the second $f=0$ and $|I_v|=2g+2q\delta$. Using the two actual lower angles moves the left part left by $d_+$ and the right part right by $d_-$. They remain disjoint after clipping to $I_v$, losing at most $d_++d_-$ in total measure. Every surviving angle is a forbidden endpoint sum for $2U_v$. Its two half-angle preimages have combined measure equal to the measure of the surviving set. Thus $|S_+|+|S_-|\le W(v)-|T_v|+h(x)$ after $\eta\downarrow0$. Endpoints crossing the angular seam cause no additional loss because clipping is done in the chosen lift before projection.

If $|K_x|=0$, the edge choices need replacing. On the first source band the whole-circle estimate gives $|T_u|-W(u)\le q(J-u)/2+\omega(u)$. On the second the envelope gives $|T_u|-W(u)\le g\le q(G-V)$. Both deterministic bounds are at most $\lambda_0=qJ/2=q(G-V)\le h(x)$, and $W(v)-|T_v|\ge0$. In both null and positive cases we have therefore proved
$$
 |T_u|-W(u)+|T_v|-W(v)\le h(x)+\mathbf1_{(0,J)}(u)\omega(u).
$$

## Integration and equality

Integrate this inequality on the two source intervals. Each target deficit is used once. On the central interval use the direct estimate on $U_u$, which costs no lower holes. On the remainder of $u\ge G$ use $|T_u|\le W(u)$. Restoring $U_u$ from $T_u$ outside $(J,V)$ costs at most $2\int_{(0,J)\cup(V,1/2)}h$. The two lower-row images additionally cost $\int_0^J h+\int_{J/2}^J h$. Finally the change of total lower area is $P-\int h$. Collecting gives the four coefficients displayed above. All changes of variables preserve null sets. With only deletions in the central band the lower area is fixed at its prescribed value, and the original upper polygon witnesses equality. [Attaining polygon and carry certificate](https://github.com/Deldor14/open-math-agents/tree/0d8d57f4a3898285fe9db73305d898aa0a36b99f/research/erdos142-deterministic-shell)

## Reproduction and attribution

The cross-row argument is a written proof for review. DoubleSum.lean proves the two-translates measure inequality on the real line and the almost-everywhere integral inequality for a translated interval. It was checked with Lean 4.33.1 and Mathlib. The inherited robust angular estimate has a separate Lean proof. The new verifier checks the shifted maps and budgets at the endpoints of their affine pieces in $\mathbb Q(\sqrt2)$, and exercises the two measure estimates on finite unions of cells. To run it, pass the directory containing verifica_parametro.py and verifica_poligono.py from the [attaining polygon certificate](https://github.com/Deldor14/open-math-agents/tree/0d8d57f4a3898285fe9db73305d898aa0a36b99f/research/erdos142-deterministic-shell).

    python3 check_stability.py /path/to/erdos142-deterministic-shell

The geometric construction track supplied the fixed-lower comparison and its two-row transport. The verification track supplies the measurable-deletion estimate and the shifted pairing here. The geometric track has separately studied continuous changes to affine lower boundaries. [Affine lower boundaries](https://github.com/Deldor14/open-math-agents/blob/8b0352129fed915c7126bec81880a7be5b73a8fd/research/erdos142-two-arc-height/AffineBases.md)
