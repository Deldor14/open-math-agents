# A second isogeny descent for 328 split septic signatures

**Mathematical argument submitted for review.** For every prime $p$ in `exponents.txt`, positive coprime integers $a,b$ cannot satisfy $a^7+b^7=C^N$ when $p\mid N$. There are 328 primes in this list, from 13 to 19963. Together with the disjoint 606 inert primes in the companion note this gives 934 exponents. For $p=13,29,41,43,71,83$ we also verify the entry condition for arbitrary signs: every primitive integer solution of $a^7+b^7=c^p$ has $abc=0$. In particular the statement about $(7,7,13)$ has no size or separation bound.

The first descent at a split prime excluded only $v_p(ab)=2$. This note aligns the local lifts at *every* depth. The additional input is Tzermias's explicit second descent function for a quotient of the Fermat curve. We give a residue calculation of this function in a totally ramified field of degree $p(p-1)$. The finite checks and the proof below are provided for mathematical review. [First split-prime descent](https://github.com/Deldor14/open-math-agents/tree/faaa9111c405767455ecea4b7164fb839ea1c612/research/beal-septic-local/split-signatures) · [Inert-prime proof, formal Picard construction and class-number certificates](https://github.com/Deldor14/open-math-agents/tree/22cfef2f5a0350008e7c9f7b4d9e061513204e1d/research/beal-septic-local/inert-signatures)

## 1. Entry and the two curves

Let $K=\mathbb Q(\theta)$ with $\theta=\zeta_7+\zeta_7^{-1}$, $M=K(\xi)$ for $\xi=\zeta_p$, and $p\equiv\pm1\pmod7$, $p\ge11$. Assume $p\nmid h(M)$. This was checked for all 328 primes by two relative class-number algorithms. Suppose a primitive nonzero solution has $p\mid ab$. The previous entry certificates give this implication for positive solutions when $p\mid N$, $p\le20000$. For signed bases and the six primes below 100 we use instead Dahmen–Siksek Proposition 4.1, valid for primitive integers, and the direct mod-$p^2$ test in `entry.gp`. Indeed $7\nmid a+b$ by BCDF and $7\nmid c$ follows by reduction modulo 7. Thus $a+b\zeta_7$ is a $p$th power. In the chart $t=a/b$ with $p\nmid b(a+b)$ the Frobenius test gives $(t+1)(t+z)^p=(t+1)^p(t+z^p)\bmod p^2$ at $z=\zeta_7$. Only $t=0\bmod p^2$ passes. If $p\mid a+b$, then $p^2\mid a+b$ and the $p$th power $(a+bz)^6/Q$ would reduce to $(z-1)^6/7$ where $Q=(a^7+b^7)/(a+b)$, contradicting the other Frobenius test in the file. Interchange the bases when needed. [Positive entry certificates](https://github.com/Deldor14/open-math-agents/tree/5e09277936d7982674b1f3ae489bc0cdace3b7cc/research/beal-septic-local/units) · [Dahmen–Siksek, §4.2](https://arxiv.org/pdf/1309.4030#page=16) · [BCDF II, Theorem 1.4](https://arxiv.org/html/2308.07062v2#S1)

Set $S=ab/(a+b)^2$ and $e=v_p(S)$. As in the first descent, $e\ge2$ by the elementary identity $(a+b)^6-Q=7ab(a^2+ab+b^2)^2$. With $d_1=2-\theta$, $d_2=4-\theta^2$ and $d_3=1+\theta+\theta^2$, the three factors $F_i=1-d_iS$ are $p$th powers $G_i^p$ in $K$. To recall the argument, their ideals are $p$th powers by the coprime factorization over $\mathbb Q(\zeta_7)$ and the extension of degree two down to $K$. They are $p$th powers at all places over $p$ since they are 1 modulo $p^2$. Adjoining the radical to $M$ is everywhere unramified, hence trivial; taking norms gives the roots in $K$.

Both curves have equation $T(T-1)=uX^p$, with $u=T_0(T_0-1)$ a global unit, $P_0=(X,T)=(1,T_0)$ and $Y_0=2T_0-1$. Select the row specified by the certificate.

| Model | $T_0$ | $T$ | $X$ | $W$ |
|---|---|---|---|---|
| 0 | $\theta+2$ | $T_0 F_1/F_2$ | $G_1/G_2^2$ | $2d_2-d_1$ |
| 1 | $(d_2-d_3)/(d_2-d_1)$ | $T_0 F_1/F_3$ | $G_1G_2/G_3^2$ | $2d_3-d_1-d_2$ |

For model 0, $T-1=(T_0-1)/F_2$. For model 1, $T-1=(T_0-1)F_2/F_3$; indeed $T_0(d_2-d_1)=d_2-d_3$. In the second model $T_0=2-\theta-\theta^2$ and $u=3-\theta^2$ have norm $-1$, and $T_0-1$ has norm 1. The equations give a point $P$ over $K$. At each of the three places over $p$, $X-1\equiv p^{e-1}s W\pmod{p^e}$, $s=S/p^e\bmod p\ne0$, by expansion of $G_i^p$.

## 2. Two global Kummer conditions

On the Jacobian $J$ let $\tau(X,T)=(\xi X,T)$ and $\lambda=1-\tau_*$. Write $H=[(0,0)-(0,1)]$ in $(X,T)$ coordinates. It generates the rational kernel of $\lambda$: the class $[(0,0)-\infty]$ generates it by the divisor of $T$ and $\deg\lambda=p$, and $H$ doubles that generator by the divisor of $X$. Write $D=[P_0-(0,1)]$. The Kummer map $\delta:J(M)/\lambda J(M)\hookrightarrow M^\times/M^{\times p}$ is evaluation of $T$ on divisors. In particular $\delta(D)=T_0$ and $\delta(H)=u$ in this quotient. At $(0,0)$ the leading coefficient of $T$ in the local parameter $X$ is $-u$, and $-1$ is a $p$th power. As in the companion paper, every valuation of a global Kummer class is a multiple of $p$ and the class is represented by a global unit. If a global point has a local lift at all three places over $p$, it has some global lift: the associated Kummer extension is unramified away from $p$ by the valuation condition, and split above $p$.

**Second division lemma.** If $V\in J(K)$ and $\delta(V)=1$, then $V\in\lambda^2 J(M)$. Take a global $\lambda$-lift. For $\sigma_a(\xi)=\xi^a$, $a\in\mathbb F_p^\times$, let $U_a=(1-\tau_*^a)/(1-\tau_*)$. The operators $U_a\sigma_a$ give a group action on the torsor of lifts of $V$, since $U_a\sigma_a(U_b)=U_{ab}$. This torsor is an affine line over $\mathbb F_p$. Averaging any orbit with weights $1/(p-1)$ gives a fixed lift $L$. Since $T$ is invariant under $\tau$, $\delta(U_a L)=\delta(L)^a$. Thus $\sigma_a\delta(L)=\delta(L)^{a^{-1}}$. In particular the unit class $\delta(L)$ is in the minus part for complex conjugation. This part of $\mathcal O_M^\times/\mathcal O_M^{\times p}$ is generated by $\xi$, since for a unit $w$ the ratio $w/\bar w$ is a root of unity and 2 is invertible mod $p$. The conductor $7p$ precludes a primitive $p^2$th root in $M$. The action on this line has character $a$, distinct from $a^{-1}$ for $p\ge5$. Hence $\delta(L)=1$ and the second division exists.

For $C\in J(K)$, evaluation on a $K$-rational divisor represents $\delta(C)$ in $K^\times$. One may choose a divisor disjoint from the zeros and poles using the rational point at infinity. The valuation argument applies directly in $K$, whose class number is prime to $p$ (by norm and extension of ideals to $M$, of degree $p-1$). Thus $\delta(C)$ comes from a unit of $K$. A nonzero determinant of the local Fermat quotients of $T_0,u$ at two places proves that these units form a basis of $\mathcal O_K^\times/\mathcal O_K^{\times p}$, of dimension two. We verify this determinant for every row. It follows that some $r,t\in\mathbb Z$ satisfy
$$ C-rH-tD\in\lambda^2J(M). $$

## 3. A local test for the coefficient of D

Fix one of the three places. Here $T_0\in\mathbb Z_p^\times$, $T_0-1$ is a unit, and $k=\mathbb Q_p(\xi)$. Write $t_0=T_0\bmod p\in\{2,\ldots,p-1\}$ and $q=(T_0^{p-1}-1)/p\bmod p$. Select a place with $q\ne0$. In $E=k(\alpha)$, $\alpha^p=T_0$, every unit of $\mathbb Q_p$ is a $p$th power: the unit quotient in $\mathbb Q_p$ has order $p$ and is generated by $T_0$. Thus our curve becomes the untwisted Fermat quotient $V^p=T(1-T)$ on scaling $X$ by a $p$th root of $-u$. The branch generator $H$ is in $\lambda^2J(E)$, since the untwisted $J[\lambda^3]$ is rational over $\mathbb Q(\xi)$. The test below shows $D\notin\lambda^2J(E)$.

**The descent function.** On the Fermat curve $x^p+y^p=1$ the quotient map can be taken as $(x,y)\mapsto(T,V)=(x^p,xy)$, with deck generator $(x,y)\mapsto(\xi x,\xi^{-1}y)$. Both endpoints of $D$ have lifts over $E$, the first with $x=\alpha$, $y^p=1-T_0$, the second with $x=1$, $y=0$. The choice of the untwisting scalar or of the second root can be made so that the product $xy$ equals the required $V$.

Tzermias's Theorem 2 for $s=1,m=1$ gives a function $f=\mathrm{Norm}(g_1)$ on this quotient with divisor $pE_1$, where the class of $E_1$ generates $J[\lambda^2]$. In his coordinates divide each affine Fermat coordinate by his primitive $2p$th root $\epsilon$; then his $h_1$ is $(1-x)/y$. His finite Hilbert-90 sum for $g_1$ gives the coboundary relation with $h_1$ (or its inverse and a deck translate according to generator). Telescoping the norm shows that, modulo $p$th powers in the Fermat function field and up to inversion, its pullback is
$$ R(x)=\prod_{i=1}^{p-1}(1-\xi^i x)^i. $$
Indeed $\mathrm{Norm}(g)/g^p=\prod_{i=0}^{p-2}(\sigma^i(\sigma g/g))^{p-1-i}$. The $y$ exponents contributed by $h_1$ total a multiple of $p$ and $\sum i^2=0\pmod p$ for $p\ge5$. Shifting the indices of the numerator multiplies its class by a power of $\prod_i(1-\xi^i x)=1-x^p=y^p$. The pullback expression is regular and nonzero at both endpoints of the lifted divisor. By the evaluation pairing (or by moving the divisor on the Fermat curve), its value on that difference is $R(\alpha)/R(1)$ up to inversion and $p$th powers. Constants cancel on degree zero. If $D=\lambda^2 B$, the $p$-Kummer pairing against $E_1$ must be trivial by functoriality, since $(\lambda^\vee)^2$ kills $E_1$ under the principal polarization. Thus a non-$p$th-power ratio rules out the second lift of $D$. [Tzermias, *Explicit Rational Functions on Fermat Curves and a Theorem of Greenberg*, pp. 337–342, Theorems 1–2](https://doi.org/10.1023/A:1002461930939)

**Computing the ratio.** Define $L_j(t)=\sum_{i=1}^{p-1}t^i/i^j$ in $\mathbb F_p$. We claim that
$$ 2L_2(t_0)-q L_1(t_0)\ne0 \quad\Longrightarrow\quad R(\alpha)/R(1)\notin E^{\times p}. $$
Let $b=\alpha-t_0$, $\pi=\xi-1$, $Q=(T_0-t_0^p)/p\bmod p=-t_0q\ne0$. The polynomial $(b+t_0)^p-T_0$ is Eisenstein. The two ramification degrees $p$ and $p-1$ are coprime, hence the absolute ramification index of $E$ is $m=p(p-1)$ and its residue field is $\mathbb F_p$. In the integer valuation of $E$, $v(b)=p-1$, $v(\pi)=p$, and $w=\pi/b$ is a uniformizer.

Up to $p$th powers the ratio is represented by
$$ B=\prod_{i=1}^{p-1}\left(\frac{1-(1+\pi)^i\alpha}{1-\alpha}\cdot\frac{i\pi}{(1+\pi)^i-1}\right)^i. $$
The normalizing rational unit $\prod i^i$ is a $p$th power in $E$, and $\sum i=p(p-1)/2$ absorbs the other constant factors. Signs in $R(1)$ are harmless for odd $p$.

Compute in characteristic $p$ through degree $p-2$ in $\pi$, treating $x$ as a variable near $t_0$. Put $s=\log(1+\pi)$. In the logarithm of the displayed product the common term $\log(\pi/s)$ is multiplied by $\sum i=0$. For degree $n$, $1\le n\le p-2$, the other coefficient in $s$ is
$$ \left(\sum_{i=1}^{p-1} i^{n+1}\right)[Z^n]\left(\log\frac{1-xe^Z}{1-x}-\log\frac{e^Z-1}{Z}\right). $$
All truncations use factorials through $(p-1)!$ and denominators prime to $p$. Only $n=p-2$ survives, with sum $-1$. At this odd degree greater than 1 the second logarithm contributes zero, since it is $Z/2$ plus an even series. Expanding the first gives coefficient $F(x)=L_2(x)/(1-x^p)$ after multiplication by $-1$: apply $(x\,d/dx)^{p-3}$ to $x/(1-x)$ and use $(p-2)!=1$ in $\mathbb F_p$. In particular $F'(t_0)=L_1(t_0)/(t_0(1-t_0))$. Exponentiating the top term and substituting $x=t_0+b$ gives
$$ B\equiv1+\pi^{p-2}(F(t_0)+F'(t_0)b)\pmod{w^{m}}. $$
Higher powers of $\pi$, and quadratic terms in $b$ in this final coefficient, have weight at least $m$.

The quotient modulo $w^m=(p)$ has characteristic $p$. A $p$th power with this expansion and residue 1 can only differ from 1 by $c w^{p(p-2)}$ modulo $w^m$, $c\in\mathbb F_p$: in a uniformizer expansion only multiples of $p$ survive. The two weights retained above are $p(p-2)$ and $p(p-2)+p-1=m-1$. From $b^p/p=Q-t_0^{p-1}b+O(b^2)$ and $\pi^{p-1}/p=-1+O(\pi)$, one obtains, up to a nonzero constant factor,
$$ w^{p(p-2)}\equiv\pi^{p-2}\big(1+(p-2)t_0^{p-1}b/Q\big)\pmod{w^m}. $$
Thus root existence requires $Q F'(t_0)+2F(t_0)=0$. Multiplication by $1-t_0$ gives the stated finite test, including when $F(t_0)=0$.

## 4. Aligning every local division

Let $A=[P-P_0]$, and let $B_{i,v}$ be its canonical formal $\lambda^i$-lift at the three places $v\mid p$. For $0\le i\le n=(p-1)(e-1)-1$ these belong to formal depth $(p-1)(e-1)-i\ge1$ by the integral formal Picard construction of the companion proof. Suppose the common global $B_{i-1}$ has been obtained, starting with $B_0=A$. Since its local Kummer classes vanish above $p$, it has a global $\lambda$-lift. At each place its difference from $B_{i,v}$ is a multiple of $H$.

If $(p-1)\nmid i$, the character averaging in the first split-prime proof makes the three lifts global: sum $U_a^i\sigma_a$ on the global lift. Locally this equals $(p-1)B_{i,v}$ because $\sum a^i=0\bmod p$. Subtract the result from the common global representative of $pB_{i,v}$.

If $i=(p-1)h$, write $p^h=\lambda^i V$ with $V\in\mathbb Z[\tau_*]^\times$. Apply $V^{-1}$ to the chosen global lift and call the point $C$. At each place
$$ C=B_v^*+k_vH,\qquad B_v^*=V^{-1}B_{i,v},\qquad p^h B_v^*=A. $$
The canonical formal $B_v^*$ is fixed by $\mathrm{Gal}(M_v/K_v)$: it is the unique solution in the formal neighborhood of its given depth, by formal division. As $H$ is also fixed and the full group $\mathrm{Gal}(M/K)$ stabilizes each $v$, localization implies $C\in J(K)$. At every such critical index the remaining formal depth is a positive multiple of $p-1$, so $B_v^*$ is locally $\lambda^2$-divisible.

Apply §2 to $C$. For suitable $r,t$, $C-rH-tD$ is globally $\lambda^2$-divisible. Pass to the field $E$ at the selected place in §3. The formal term and all multiples of $H$ are $\lambda^2$-divisible there. The explicit obstruction for $D$ forces $p\mid t$, since $J(E)/\lambda^2J(E)$ is killed by $p$. At each of the original three places, $\delta(C-rH)=u^{k_v-r}=1$. Our finite test requires the Fermat quotient of $u$ to be nonzero at *every* place. Consequently $u$ is nontrivial modulo $p$th powers in $\mathbb Q_p$ and remains so after the degree-$p-1$ extension to $M_v$. Hence $k_v=r$ at all three places. Now $V(C-rH)$ realizes the three canonical $B_{i,v}$ globally. This closes the induction at all depths.

At the last index the global point has formal depth one at all three places. Its local Kummer class has a representative in $1+\pi^p$ at all three, giving an everywhere unramified extension by the Artin–Schreier reduction used in the companion paper. Hence its class is trivial. The interpolation computation there, valid for both models through their displayed leading tangents, gives its coefficient at depth $p$ as a nonzero prime-field scalar times $Wu/Y_0^3$ at each place. A local $p$th power at this depth has trace-zero coefficient. The residue fields here are $\mathbb F_p$; the certificates check $Wu/Y_0^3\ne0$. This contradiction completes the argument.

## Checks

Each row of `certificates.txt` gives $p$, model, residue of $\theta$ at the selected place, $t_0$, $q(T_0)$, $q(u)$, the determinant of the two unit columns at the first two places in increasing residue order, $Wu/Y_0^3$ at the selected place, and the finite-dilogarithm obstruction. Both programs also check $q(u)$ and the tangent at the two other places. Model 1 is used for 13 and 41. At $p=13$, the selected place has $\theta=7$, $T_0=141\bmod169$, $q=2$, $L_1(11)=8$, $L_2(11)=10$, and the obstruction is 4. The direct computation in the degree-156 local field tests all 13 choices for the leading root correction. The largest weight attained is 155, short of the required 156. The direct formal products, explicit local field and Lean file separately check parts of the calculation. The isogeny and class-field arguments above are written proofs.

Run in this directory with Python 3.9+, PARI/GP and, for the last check, Lean with Mathlib. The prime list is the full passing split list of the earlier class-number computation.

```sh
python3 check.py > replay.txt
cmp replay.txt certificates.txt
gp -fq -s 120M independent.gp
python3 product.py
gp -fq -s 160M field13.gp
gp -fq -s 120M entry.gp
lean SepticThirteen.lean
```
