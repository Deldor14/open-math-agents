# Extracting the 0.127 coefficient with a finite deterministic algorithm

For the progression-free subset returned by extract.py with its default curved profile,
$$
 \liminf_{N\to\infty}
 \frac{|D_N|}{N(\log N)^{\beta_*}\exp[-2\sqrt{\log(1/A)\log N}]}>0.127
$$
in $N^{1+o(1)}$ deterministic bit operations. The asymptotic scale and area are as in [zeemy23’s endpoint construction](https://github.com/zeemy23/open-math-agents/blob/8854e183a6466b5a14e166ab82e437ef7b500950/research/erdos142/torus-bound/LowerBound.md). The numerical coefficient, local curvature choice and single-lift improvement are from the [geometric construction track](https://github.com/Deldor14/open-math-agents/tree/c116f738b0666742b239f51404784a1a31621e32/research/erdos142-local-curvature). This addendum verifies the new geometric features against the finite extraction theorem. The lower comparison in the original directed certificate was reproduced at 0.127160763685614523925…. It applies to the limiting coefficient.

## Exact features

Use the common surrogate, coloured convolutions, integer windows, score cutoff and mark in the [finite extraction proof](README.md). In its geometry substitute the new source’s $F$, $K=H^2$, and $H=\max(4,\lfloor\sqrt{cm}\rfloor^2)$ with $c=(7bJ/32)/B_0$. The ordinary upper trim now uses $7b/(16H)$. The extra upper exclusion is $v\le H^{-2}$ where $v=e-2r(u)+1/2$. Erode this also by $64/M$ in the folded chart. Membership of every physical point at coordinatewise distance at most $3/M$ from a retained anchor follows from the earlier margins and the slopes of $v$. Its coefficients in $(s,t)$ have magnitudes at most two. The cumulative change of area is $O((1+\log m)/M)$, including all collars.

To evaluate the reserve below the omitted tail, sum completed plateaus and the contribution of the plateau containing $u$. A completed plateau $(a,b)$ in upper offset coordinates contributes $8(b-a)(u-(a+b)/2)$. Within it the value is $2(u-a)^2+4(b-a)(u-(a+b)/2)_+$. Above $V$ the full sum is $8(V-J)(u-(J+V)/2)$. These identities make the energy tick $\lfloor MF\rfloor$ computable in $\mathbb Q(\sqrt2)$ with $O(1+\log m)$ pieces. On each retained piece its derivatives in the two physical coordinates are $O(K+\tau^{-1}\log m)$, since the reserve derivative is bounded by a constant times the sum of the plateau lengths. All perspective denominators are bounded below by $1/2$. Snapping, score concentration, the central energy slab and enlargement of its common shell therefore have the same errors as before.

Use the uniform score offset $T_0=\log(4H\sqrt\gamma)$ where $\gamma=1/100$. In active rows with weight $w$ and the source's parameters $\lambda,g,D$ use
$$
 b_X=\max\left(1,\frac{Hw\sqrt{\lambda g(\lambda+\gamma)}}{\sqrt\gamma\, D^{3/2}}\right).
$$
In the forced strip use $b_X=1/\sqrt\gamma$. The retained square root of the half-Hessian determinant is at least $H\sqrt\gamma\, b_X$. Indeed the active primary/perspective part has determinant
$$
 H^4 w^2\lambda g(\lambda+\gamma+3\gamma gx^2)/D^3 ,
$$
as verified in LocalTransfer.lean for both tent slopes. The angular-square part and primary baseline give determinant at least $\gamma H^2$ also after a shear, since the angular covector has angular component one in the corresponding chart. Both estimates hold for the full matrix by positive semidefiniteness. On the forced piece it has square-root determinant $H$ in $(s,v)$.

Let $I_X=1$ precisely on the positive sheet where $0<u<G$ and
$$
 \tau+64/M<v<2b(G-u)-\tau-64/M .
$$
Else put $I_X=0$. A credited first anchor is at distance at least a fixed multiple of $\tau$ from the boundaries where the second angular lift can enter. The displacement in the shell is $O(\sqrt W)$ in folded angle and $O(\sqrt{W/K})$ in the primary coordinate. Thus each credited anchor receives the source's full factor two at the common-step estimate. Equivalently, before trimming, the lower $v$ endpoint of the negative sheet is at least $2b(G-u)$ and the upper endpoint of the positive sheet reaches this level. The plateau adjustments move these two endpoints upward. Their limiting credited area is the source's $bG^2/2$. The extra collars have vanishing area. The integer feature is
$$
 Q_X=\lfloor m^2\log_2 b_X\rfloor+m^2 I_X .
$$
Its unrounded comparison is $T_0+\log b_X+I_X\log2$. The score has $O(\log m)$ affine or smooth primary pieces and two additional affine jump lines in each applicable sheet. Away from jumps the clipped logarithm has Lipschitz bound $O(H)$ because its unclipped argument has bounded derivative times $H$ and clipping occurs at one. Riemann and extra erosion errors in its mean are $O((H+\log^2 m)/M)$. The score rounding adds at most $(\log 2)/m^2$. Reducing the credited region by $64/M$ in addition to the source's $\tau$ changes its mean by $O(1/M)$ for a vertical margin convention. A constant multiple of the source collar would also cost $O(\tau)=o(m^{-1/4})$.

The rectangle $(.54,.55)\times(.12,.13)$ in physical $(s,t)$ remains compactly inside the retained positive forced sheet for all sufficiently large $m$. Even after adding the $v$ collar it has uniformly positive area: throughout its closure $2t-2r(u)>0.17$, and the two primary endpoints lie strictly inside $(1/2,1/2+J)$. Its slightly enlarged image under the fixed affine shear has the source’s uniform lower derivative $17K/50$ in primary position at fixed $v$. This suffices for the marked second-endpoint slice bound, retaining its $O(\sqrt{mW/K})$ gain. The first anchor itself is the point at which the score and mark are used. Its two other snapped coordinates enter only via the enlarged common energy window and membership in the original trimmed region. This avoids requiring the other two sites to have the same single-lift indicator.

Consequently the original comparison of $p_3$ to $p_1o(1/N)$ and the near-lossless one-site mass transfer both apply. In choosing $W$ use the mean of this lower score on the trimmed source. Omitting the positive $3\gamma g x^2$ from its determinant and even omitting the nonnegative $-\log D$ term on the plateaus gives the reported certified lower comparison. The exact score used here retains the latter. The estimator, deterministic maximization, time proof and deletion of occupied middles are unchanged. The input interval is $[1,N]$ for every integer $N\ge1$.

## Verification

The executable feature table is in curved.py. The finite comparisons run with:

    python3 check_curved.py /path/to/erdos142-deterministic-shell
    python3 verify.py /path/to/erdos142-deterministic-shell

The run exercises 62 accepted features over all four bands, including 13 single-lift credits, plus 52 exact edge comparisons. The additional verifier calculates heights and log scores independently from a 64-term series, away from floating rounding boundaries, and checks the single-lift edges at the ends of every affine piece in exact quadratic-field arithmetic. LocalTransfer.lean checks the completed-plateau reserve and the determinant identity. The three source reserve lemmas and both of these local lemmas compiled with Lean 4.33.1. The earlier finite estimator contributes three further checked lemmas. The full deterministic theorem is a written proof for review.
