# A cyclotomic descent and a formal-group obstruction for the signature (7,7,11)

**Result submitted for review.** If coprime integers satisfy $a^7+b^7=c^{11}$, then $abc=0$. Both signs and arbitrarily large bases are allowed. Dahmen and Siksek obtained this conclusion under GRH via a rank computation for a genus-five Jacobian. We use their cyclotomic reduction, and the unconditional exclusion of the ramified branch by Billerey, Chen, Dieulefait and Freitas. The new argument uses the isogeny $1-\zeta_{11}$ and the motion of a point in a residue disk. It does not require the rank of the Jacobian or the class group of the nonabelian degree-33 field of the two-descent. This is a written mathematical argument with reproducible finite checks. [Dahmen–Siksek, §§4–5](https://arxiv.org/pdf/1309.4030) · [BCDF II, Theorem 1.4(1)](https://arxiv.org/html/2308.07062v2#S1)

## 1. The putative point

Suppose $abc\ne0$. Set $D=a+b$, $Q=(a^7+b^7)/D$, $z=\zeta_7$, $\theta=z+z^{-1}$ and $K=\mathbb Q(\theta)$. Thus $\theta^3+\theta^2-2\theta-1=0$. BCDF give $7\nmid D$. Since $\gcd(D,Q)=1$, write $D=v^{11}$, $Q=w^{11}$. Dahmen–Siksek Proposition 4.1 yields $a+bz=\beta^{11}$ in $\mathbb Z[z]$.

We first need $11^2\mid ab$. Here is a small check independent of any earlier large table. Use the chart $11\nmid b$, with $t=a/b$, and interchange $a,b$ if necessary (the pure-power result applies in either order). If $11\nmid D$, the integral local element $(t+z)/(t+1)$ is an eleventh power. The unramified Frobenius $z\mapsto z^{11}$ therefore agrees with its eleventh power modulo 121, also at a nonunit numerator. In $(\mathbb Z/121)[Z]/\Phi_7$ the check is $(t+1)(t+Z)^{11}=(t+1)^{11}(t+Z^{11})$. The only residue $t$ modulo 121 passing it with $11\nmid t+1$ is zero. If $11\mid D$, then $121\mid D$. The local eleventh power $(a+bz)^6/Q$ reduces to $(z-1)^6/7$ modulo 121, and this fails the same Frobenius test. `entry.py` checks both statements by cyclic multiplication: two coefficient vectors of length seven agree modulo $\Phi_7$ exactly if their differences are constant. It follows that $11\nmid D$ and that $S=ab/D^2\in\mathbb Q^\times$ has $e=v_{11}(S)\ge2$.

Write $d_1=2-\theta$, $d_2=4-\theta^2$, $u=(\theta+1)(\theta+2)$, $Y_0=2\theta+3$, and $W=2d_2-d_1=6+\theta-2\theta^2$. The conjugates $\theta_1=\theta$ and $\theta_2=\theta^2-2$ give elements $G_i\in K$ with $G_i^{11}=1-d_i S$: take conjugates of $\beta\bar\beta/v^2$. Define

$$X=G_1/G_2^2,\qquad Y=(Y_0-d_2S)/(1-d_2S).$$

The identity $(Y_0-d_2S)^2=(1-d_2S)^2+4u(1-d_1S)$ puts $(X,Y)$ on $C:Y^2=1+4uX^{11}$, the curve $C_{11,3}$ of Dahmen–Siksek. Its point $P_0=(1,Y_0)$ belongs to $C(K)$. The prime 11 is inert in $K$, and its completion is unramified with residue field $k_0=\mathbb F_{11^3}$. Each $G_i\equiv1\pmod{11}$ since its eleventh power is 1 in the residue field. For $s_0=S/11^e\bmod11\in\mathbb F_{11}^\times$ and $h=e-1\ge1$, the binomial expansion gives

$$X-1\equiv 11^h W s_0\pmod{11^{h+1}},\qquad Y\equiv Y_0\pmod{11}.$$

Indeed $v_{11}((1+t)^{11}-1)=1+v_{11}(t)$ for $t\in11\mathcal O_{K_{11}}$ and the leading term is $11t$. Both $d_i$ and $W,Y_0$ have nonzero residues. The rationality of $s_0$ will matter in the last trace.

## 2. Global Kummer classes detected at one prime

Let $M=K(\xi)$, $\xi=\zeta_{11}$, $k=M_{\mathfrak l}$ at its unique prime above 11, $\pi=\xi-1$. The residue is still $k_0$ and $11/\pi^{10}\equiv-1\pmod\pi$. Use $T=(Y+1)/2$, so $T(T-1)=uX^{11}$. Write $J=\operatorname{Jac}(C)$, $\tau(X,T)=(\xi X,T)$ and $\lambda=1-\tau_*$ on $J$. All points of $J[\lambda]$ are rational over $M$. Indeed $H=[(X,T)=(0,0)-\infty]$ is a nonzero point of order 11 by the divisor of $T$ and the positive genus. It is fixed by $\tau$. On the five regular differentials $X^{j-1}dX/Y$, $1\le j\le5$, the eigenvalues of pullback by $\tau$ are $\xi^j$. Together with their complex conjugates they give all ten primitive characters, so $\deg(1-\tau_*)=11$. The dual isogeny has the same kernel under the principal polarization since $1-\tau_*^{-1}$ differs from $1-\tau_*$ by an automorphism.

Over $M$ or $k$, evaluating $T$ on degree-zero divisors away from its zeros and poles gives the injective Kummer map $J(F)/\lambda J(F)\to F^\times/F^{\times11}$. This is the descent map obtained by pairing the connecting homomorphism with the generator $H$ of the dual kernel; $\operatorname{div}(T)=11H$ in divisor notation. The point at infinity permits degree-zero divisor representatives, and the moving lemma permits this choice of support. Values at closed points use field norms. In particular a difference of two ordinary points has image the ratio of their $T$-coordinates. [Schaefer, *Computing a Selmer group of a Jacobian using functions on the curve*](https://arxiv.org/abs/1507.08325) · [Poonen–Schaefer, *Explicit descent for Jacobians of cyclic covers*](https://math.mit.edu/~poonen/papers/descent.pdf)

Every global Kummer class is represented by a global unit. The element $u$ is a unit (the norms of $\theta+1$ and $\theta+2$ are $-1$ and $1$). At every finite place of a point's field of definition, a positive valuation of $T$ makes $T-1$ a unit, and a negative one gives $v(T-1)=v(T)$. The equation implies $11\mid v(T)$ in either case. Norms preserve this divisibility. Hence the resulting principal ideal is the eleventh power of an ideal. The 11-primary part of $\mathrm{Cl}(M)$ is trivial. The reproducible unconditional Aoki–Fukuda computation is `subcyclopclgp([77,[34]],11,1)`: 34 acts by inversion on the seventh roots and fixes the eleventh roots. Its plus and minus exponents are both zero, and $11\nmid2[M:\mathbb Q]=60$. [PARI documentation, `subcyclopclgp`](https://pari.math.u-bordeaux.fr/dochtml/html-stable/General_number_fields.html#subcyclopclgp)

**Detection.** The map from $\mathcal O_M^\times/\mathcal O_M^{\times11}$ to $(\mathcal O_k/\pi^{11})^\times$ modulo eleventh powers is injective. The domain has dimension 15 over $\mathbb F_{11}$ by Dirichlet's theorem, as $M$ has signature $(0,15)$ and contains $\mu_{11}$. The finite certificate below gives 15 independent images. Thus a global point whose local Kummer value is represented by an element of $1+\pi^{11}\mathcal O_k$ is globally divisible by $\lambda$. In particular if a specified local point $B$ satisfies $\lambda B=A$ for a global $A$, then $B$ itself is global: some global lift exists by detection, and all differences of lifts lie in the rational kernel. This statement can be iterated without a rank hypothesis.

### Certificate for detection

Use $s=\xi+\xi^{-1}-2=\pi^2/\xi$. For $a=1,2,3,4$ and the three conjugates $t_b$ of $\theta$, use the global units $E_{a,b}=\xi^a+\xi^{-a}-t_b$. They factor, up to roots of unity, into numbers $1-\zeta_{77}^j$ of exact order 77 in the root-of-unity term; these factors are units since $\Phi_{77}(1)=1$. Raise local units to 1330 to remove the residue-field factor. This operation acts invertibly on the eleventh-power quotient. Every eleventh power of a principal unit is 1 modulo $\pi^{11}$.

For the four graded pieces $s^j$, $1\le j\le4$, the ring has characteristic 11 modulo $s^5$. Divide $E_{a,b}$ by its residue-field constant $2-t_b$ there (its 1330-th power is one there). The truncated logarithm of the result is additive. In the coefficient of $s^j$ the dependence on $a^2$ is a polynomial of degree at most $j$ with zero constant. The leading coefficient is the coefficient of $Z^j$ in

$$\log\left(1+H_b\sum_{i=1}^4 \frac{2Z^i}{(2i)!}\right),\qquad H_b=(2-t_b)^{-1}.$$

This follows from the recurrence for $\xi^a+\xi^{-a}$ as a polynomial in $2+s$: its coefficient of $s^i$ is $2a^2\prod_{j=1}^{i-1}(a^2-j^2)/(2i)!$. The four different nonzero squares $a^2$ give an invertible Vandermonde matrix with powers 1 through 4. Successively eliminating the preceding powers, the determinants of the three leading columns (one per $b$ in the basis $1,\theta,\theta^2$) are $5,5,8,9$ modulo 11 at the four grades. This gives 12 independent images. The unit $\xi$ gives a thirteenth at depth one. The two units $\theta,\theta^2-2$ give two more at depth ten: their 1330-th powers minus one divided by 11 have residues $(9,1,8)$ and $(9,3,4)$. These 15 images are independent already modulo $\pi^{11}$. `residue.py` verifies the determinants with cubic-field arithmetic; `global-units.gp` independently obtains rank 15 with the local multiplicative group of the absolute field.

## 3. Division on the formal group of the integral curve

Over $\mathcal O_k$ take the projective flat model with affine chart $T^2-T=uX^{11}$ and infinity chart $v^2-z^6 v=uz$, with $z=1/X$, $v=T/X^6$. This is the finite flat double cover of the projective line on these charts. Its special fibre is geometrically integral: $T(T-1)/\bar u$ is not an eleventh power in $\overline{k}_0(T)$ since its zero at 0 is simple. The single point at infinity is smooth. Use the formal completion of the relative degree-zero Picard scheme at the identity. It is a smooth formal group of dimension five. Here smoothness also follows from the line-bundle deformation obstruction $H^2(\mathcal O)=0$ for curves, and its tangent space is $H^1(\mathcal O)$. The cotangent basis dual to tangent coordinates is $\omega_j=X^{j-1}dX/Y$, $1\le j\le5$. These sections of the relative dualizing sheaf follow from the plane equation by adjunction; the chart at infinity changes $dX/Y$ into $-z^4 dz/(2v-z^6)$. They form a basis on the special fibre as well, by independence and arithmetic genus five. [Conrad, *Picard functors for curves*, §§2–3](https://math.stanford.edu/~conrad/248BPage/handouts/pic.pdf)

For clarity, integral formal coordinates can be chosen as follows. Take five smooth sections $P_i=(r_i,T_i)$ with distinct residues $\bar r_i$ and $\bar Y_i\bar T_i\ne0$. Such sections exist: residues $r_i=1,2,-1,\theta,1+\theta$ work, with $\bar Y_i$ a square root of $1+4\bar u\bar r_i^{11}$ and Hensel lifting. Perturb $X=r_i+w_i$, lifting $T$ in the same disk. Send $(w_i)$ to $\sum_i[P_i(w_i)-P_i]$. The differential of the Abel map on a smooth section pairs a tangent with a dualizing form by evaluation. The matrix of this map is $(r_i^{j-1}/Y_i)_{j,i}$, which has unit determinant by Vandermonde. Thus the map is an isomorphism of formal neighborhoods of the section and identity by the formal inverse function theorem. Degree-zero families of line bundles obtained there give points on the generic Jacobian over $k$. We only need the resulting identities in the generic Jacobian.

Write $F^m$ for the formal tuples with $w_i\in\pi^m\mathcal O_k$, $m\ge1$. The automorphism $\tau$ extends integrally, reducing to the identity on the entire special fibre. Hence *every* coefficient of the formal-coordinate expression for $\lambda$ is divisible by $\pi$. In the coordinates paired with the differentials $\omega_j$, the linear term of $\lambda/\pi$ reduces to the diagonal with entries $-j$, since $\tau^*\omega_j=\xi^j\omega_j$. This linear term is invertible, so the power series obtained by dividing the output coordinates by $\pi$ has an integral formal inverse. It follows that $\lambda:F^m\to F^{m+1}$ is bijective for all $m\ge1$ and on the graded tangent coordinates takes $v_j$ to $-j v_j$ after scaling by the appropriate powers of $\pi$. Only the formal neighborhoods are involved in this assertion.

The global divisor $A=[P-P_0]$ of §1 is represented in $F^{10h}$. In differential coordinates its leading vector, after removing $\pi^{10h}$, is a nonzero scalar in $\mathbb F_{11}$ times $(W/Y_0)_{j=1}^5$: all five forms have the same value at $X=1$, and $11/\pi^{10}\equiv-1$. Let $n=10h-1$. By formal division there is $B\in F^1$ with $\lambda^n B=A$. By the global detection and rational kernel of §2, each successive specified local lift of $A$ is a global point of $J(M)$ on the generic fibre. In particular $B$ is global. If $v_j$ are its tangent coordinates after removing one $\pi$, they satisfy

$$ v_j=c_0 j\, W/Y_0\quad(1\le j\le5),\qquad c_0\in\mathbb F_{11}^\times.$$

Indeed $(-j)^{-n}=-j$ in $\mathbb F_{11}^\times$, and the common sign is absorbed in $c_0$. All expressions in these tangent identities are in $k_0$.

## 4. The last Kummer value

Write $w_i=\pi b_i\bmod\pi^2$ for $B$ in the five-section chart, and omit bars on residue-field elements in this paragraph. Thus $v_j=\sum_i r_i^{j-1} b_i/Y_i$. The Kummer product of the five ratios $T_i(w_i)/T_i$ belongs to $1+\pi^{11}\mathcal O_k$. If the product is $1+\pi^{11}L\bmod\pi^{12}$, its coefficient is

$$L=\sum_i \frac{u}{Y_i T_i}\,(b_i^{11}-r_i^{10}b_i).$$

This follows by subtracting $T^2-T=uX^{11}$ at the two points and expanding $(r_i+w_i)^{11}$. The linear term uses $11/\pi^{10}\equiv-1$. The residue $b_i$ suffices since a change in $w_i$ by $\pi^2$ changes this expression only at order 12 or higher.

An eleventh power in $1+\pi^{11}\mathcal O_k$ must have $\operatorname{Tr}_{k_0/\mathbb F_{11}} L=0$. Its root reduces to one, and $(1+\pi b)^{11}\equiv1+\pi^{11}(b^{11}-b)\pmod{\pi^{12}}$. On the other hand the global class of $B$ is represented by a global unit and its local image is trivial modulo $\pi^{11}$. Detection makes its global Kummer class trivial, so the trace must be zero.

Here is its value from the tangent. Put $d=u^{1/11}$ in $k_0$ and $Z_i=Y_i^{1/11}$, so $Z_i^2=1+4d r_i$. For $\kappa_i=u/(Y_i T_i)$ we have $\kappa_i^{1/11}=2d/(Z_i(Z_i+1))$ and $r_i\kappa_i^{1/11}=(Z_i-1)/(2Z_i)$. Therefore

$$ Y_i(\kappa_i^{1/11}-r_i^{10}\kappa_i)=H(r_i),\qquad H(X)=\frac{1-(1+4dX)^5}{2X}.$$

This polynomial has degree four. Since trace is invariant under Frobenius, the trace of $L$ is the trace of $\sum_i H(r_i)b_i/Y_i$. The tangent formula in §3 maps a polynomial $f$ of degree at most four to $\sum_i f(r_i)b_i/Y_i=c_0(W/Y_0)(f(1)+f'(1))$. Applying it to $H$ gives

$$\operatorname{Tr}(L)=c_0\operatorname{Tr}\left(\frac{W d}{Z_0^3}\right),\qquad Z_0=Y_0^{1/11}.$$

Indeed $(XH(X))'=d(1+4dX)^4$ in characteristic 11. In the basis $1,\theta,\theta^2$ we have $d=(10,10,2)$, $Z_0=(10,0,2)$, and $Wd/Z_0^3=(10,4,0)$. The trace is **4**: the traces of $1,\theta,\theta^2$ are $3,-1,5$. Since $c_0\ne0$, this contradicts the zero trace required above. This excludes the assumed nontrivial primitive solution.

## Reproduction and verification scope

Python uses only its standard library. GP uses PARI's unconditional class-group routine and finite ray groups. Commands below were tested with PARI 2.19.1 and Lean 4.33.1 with Mathlib.

```sh
python3 entry.py
python3 residue.py
python3 tangent.py
gp -fq -s 150M class.gp
gp -fq -s 150M global-units.gp
gp -fq -s 150M local-replay.gp
lean Trace.lean
```

The elementary residue calculation and four different five-section charts give the same trace 4 after normalizing $c_0=1$. The separate GP replay Hensel-lifts two actual points above each of the five residues to precision $\pi^{12}$. Their Kummer product has valuation 11 after subtracting one. Its ray-group image modulo eleventh powers is zero at depth 11 and nonzero at depth 12. The unit-image ranks at depths 1 through 12 are $0,1,4,4,7,7,10,10,13,13,15,15$. The Lean file checks the curve identity, cubic irreducibility test and final finite-field calculation. The descent and formal-Picard arguments are written proofs for mathematical review. This concerns the single signature $(7,7,11)$ of Beal's conjecture.
