# The primitive signature (13,13,41)

Deldor14 · 28 November 2026 · Written proof for mathematical review

**Claim.** The only coprime integer solutions of $a^{13}+b^{13}=c^{41}$ have $abc=0$. The proof is unconditional and covers signed integers of arbitrary height. We eliminate one cyclotomic unit class at 163 by a modular trace comparison. On the remaining class, division on a genus-20 Jacobian forces a residue of trace zero whose computed trace is a nonzero multiple of 31.

## Excluding the extraneous unit at 163

Set $p=41$, $L=\mathbb Q(z)$ with $z=\zeta_{13}$, and $D=a+b$. Suppose $abc\ne0$. Best–Dahmen–Freitas Theorem 1.2 excludes $13\mid D$. As in their (4.3), $D=v^p$; indeed $\gcd(D,(a^{13}+b^{13})/D)=1$. Their §4.2, case I, reports its sieve through $p=43$ and leaves $a+bz=\epsilon\beta^p$ with either $\epsilon=1$ or $\epsilon=\mu=(13/(1-z)^{12})^k$ where $12k\equiv-1\pmod p$. Their list of additional sieving primes in §4.3 ends at $p=37$. We supply the following sieve at $q=163$. [Best–Dahmen–Freitas, §§4.1–4.3](https://arxiv.org/html/2510.12092v1#S4)

Suppose $\epsilon=\mu$. The order of 163 modulo 13 is 12. Write $z$ also for the image in $\mathbb F_{q^{12}}$. If $q\nmid D$, set $t=a/D\bmod q$. Then $(t+(1-t)z)/\mu$ must be a 41st power. Raising this element to $(q^{12}-1)/41$ for all $t$ from 0 to 162 gives **no** value equal to one. None of the tested numerators vanish. An independent enumeration uses $t+z/(1-z)$ as the test element, since $\mu/(1-z)$ is a 41st power times a rational scalar and $\gcd(41,q-1)=1$. Thus $q\mid D$.

The residual representation of the Frey curve $E_{a,b}$ over $\mathbb Q(\sqrt{13})$ must match one of $E_{1,0},E_{1,1}$, by Best–Dahmen–Freitas Proposition 2.2 and the local comparison above 13 used in their §4.3 (since $13\nmid D$). At 163 the Frey curve has good reduction and its reduction is isomorphic to that of $E_{1,-1}$: $a$ is a unit, $b=-a$ in the residue field, and the short coefficients are homogeneous of degrees four and six. We use the explicit model of Billerey–Chen–Dieulefait–Freitas §7.1. Put $t_j=z^j+z^{-j}$, $A=(t_4-t_3)(a^2+t_1ab+b^2)$, $B=(t_1-t_4)(a^2+t_3ab+b^2)$ and $C=-A-B$. The short coefficients are $27(AB+AC+BC)$ and $-27(2A^3+3A^2B-3AB^2-2B^3)$. [Best–Dahmen–Freitas, §4.3](https://arxiv.org/html/2510.12092v1#S4.SS3) · [Billerey–Chen–Dieulefait–Freitas, pp. 8665–8666](https://lmbp.uca.fr/~billerey/Research/Published/BCDF19_MultiFrey.pdf)

Over $\mathbb F_{163^2}$ take $h=1+t_1+t_3+t_4$, so $h^2=h+3$. The three good models have the following data.

| $(a,b)$ | coefficient of $x$ | constant | Frobenius trace | residue mod 41 |
|---|---|---|---:|---:|
| $(1,-1)$ | $13+50h$ | $66+129h$ | −11 | 30 |
| $(1,0)$ | $137+27h$ | $22+56h$ | −77 | 5 |
| $(1,1)$ | $56+h$ | $116+32h$ | −17 | 24 |

Direct counting of the points over this quadratic field and PARI elliptic arithmetic agree. Isomorphic residual representations must have equal traces at this good prime away from 41. Neither residue equals 30. This eliminates $\mu$ and gives $a+bz=\beta^{41}$.

## Entry into the 41-adic disk

The order of 41 modulo 13 is 12. If $41\nmid D$, enumerate $t=a/D$ modulo $41^2$. The unit $t+(1-t)z$ is a 41st power, so its $(41^{12}-1)$-st power is 1 modulo $41^2$. Only 0 and 1 pass. If $41\mid D$, then $41^2\mid D$ and $a(1-z)$ would be a 41st power modulo $41^2$ with $a$ a rational unit. But $(1-z)^{41^{12}-1}$ is nonscalar modulo $41^2$, giving a contradiction. The verifier independently tests Frobenius congruences in both charts. Hence $S=ab/D^2$ has finite $e=v_{41}(S)\ge2$.

Write $H=\mathbb Q(\theta)$, $\theta=z+z^{-1}$, $d_1=2-\theta$, $d_2=4-\theta^2$, $U=(\theta+2)(\theta+1)$, $Y_0=2\theta+3$, and $W=2d_2-d_1$. In $H$ the two conjugates $G_i=\sigma_i(\beta\bar\beta)/v^2$ with $\sigma_i(z)=z^i$ satisfy $G_i^p=1-d_iS$. Put $X=G_1/G_2^2$ and $Y=(Y_0-d_2S)/(1-d_2S)$. The identity $(Y_0-d_2S)^2=(1-d_2S)^2+4U(1-d_1S)$ gives a point $P$ on $Y^2=1+4UX^p$. Each $G_i\equiv1\pmod{41}$ in the unramified sextic completion, and $X-1\equiv41^{e-1}Ws_0\bmod41^e$, where $s_0=S/41^e\bmod41\in\mathbb F_{41}^\times$. This follows by expanding $G_i^p$ at 1. The reference point is $P_0=(1,Y_0)$.

## Global division and the genus-20 boundary

We spell out the changes in dimension and precision from the formal descent for the previous signature. The degree-seven work introduced the formal local argument. [Split descent for (13,13,11), §§2–4](https://github.com/Deldor14/open-math-agents/tree/c668e382272096b322b6bd376911aa89288bb304/research/beal-thirteenth-gap/split-eleven) · [Original (7,7,11) argument](https://github.com/Deldor14/open-math-agents/tree/b2d65981681cf44455709e953d70fe393a606e83/research/beal-septic-local/seven-eleven)

Set $M=H(\xi)$ with $\xi=\zeta_{41}$, and $\pi=\xi-1$. There is just one prime at 41, with residue field $k_0=\mathbb F_{41^6}$, and $41/\pi^{40}\equiv-1$. The group $\operatorname{Cl}(M)[41]$ is trivial: in conductor 533 use the subgroup of order two generated by inversion on $z$ and identity on $\xi$. The unconditional Aoki–Fukuda implementation gives $[41,[0,[]],[0,[]],[120,2],31,159]$ and $41\nmid2[M:\mathbb Q]$. [PARI, subcyclopclgp](https://pari.math.u-bordeaux.fr/dochtml/html-stable/General_number_fields.html#subcyclopclgp)

On the Jacobian $J$ let $\lambda=1-\tau_*$, with $\tau(X,Y)=(\xi X,Y)$. The function $T=(1+Y)/2$ has divisor $p((0,0)-\infty)$ in $(X,T)$ coordinates. This branch difference generates the rational kernel of $\lambda$ and its dual: the eigenvalues on holomorphic differentials are $\xi^j$, $1\le j\le20$, and together with the conjugates give degree $p$. The branch difference is nonzero by positive genus. Evaluation of $T$ on moved degree-zero divisor representatives injects $J/\lambda J$ into the multiplicative group modulo $p$th powers. From $T(T-1)=UX^p$ with $U$ a unit, valuations of every such class are multiples of $p$. The prime-to-$p$ class number allows global unit representatives. If such a unit is locally a $p$th power modulo $\pi^p$, adjoining its $p$th root gives an everywhere unramified abelian extension. Indeed at $p$ the local representative is $1+c\pi^p$ and $((1+\pi Z)^p-1)/\pi^p-c$ reduces to $Z^p-Z-\bar c$, with simple roots over a residue field extension. At other finite primes apply Hensel to the unit; all archimedean places are complex. The Hilbert class field theorem gives global triviality. In particular any specified local $\lambda$-preimage of a global point is global, by this detection and rationality of the kernel.

For the proper flat model use $T^2-T=UX^p$ and $v^2-z'^{21}v=Uz'$ at infinity ($z'=1/X$, $v=T/X^{21}$). The special fibre is geometrically integral since $T(T-1)/\bar U$ has a simple zero. The formal relative Picard group at the identity is smooth of dimension 20 by the vanishing of the line-bundle obstruction $H^2(\mathcal O)$. The integral dualizing forms are $X^{j-1}dX/Y$ for $1\le j\le20$, by adjunction and the infinity chart. For a system of integral formal coordinates take twenty smooth sections with distinct abscissas $r_i$, given in the residue by $Z_i=2,3,\ldots,20,\bar\theta$, $r_i=(Z_i^2-1)/(4d)$, $Y_i=Z_i^p$, $d=U^{1/p}$. All $Y_iT_i\ne0$. Hensel lifts these sections and the Abel differential in their abscissa displacements is the invertible matrix $(r_i^{j-1}/Y_i)_{j,i}$. Thus this chart identifies the formal neighborhoods. [Conrad, Picard functors for curves](https://math.stanford.edu/~conrad/248BPage/handouts/pic.pdf)

Since $\tau$ is the identity on the special fibre, all formal coefficients of $\lambda$ are divisible by $\pi$. The derivative of $\lambda/\pi$ in differential coordinates reduces to the diagonal with entries $-j$ and is invertible. The formal inverse theorem gives a bijection from depth $m$ to $m+1$ under $\lambda$ for every $m\ge1$. The point $[P-P_0]$ has initial depth $40(e-1)$ and vector with each entry a common $\mathbb F_{41}^\times$ multiple of $W/Y_0$. Divide formally $40(e-1)-1$ times. All the prescribed preimages are global. At depth one the final point has coordinates $v_j=c_0jW/Y_0$, $c_0\in\mathbb F_{41}^\times$, since $(-j)^{1-40(e-1)}=-j$.

Writing the twenty abscissa displacements as $\pi b_i\bmod\pi^2$ gives $v_j=\sum_i r_i^{j-1}b_i/Y_i$. The Kummer product of displaced to original $T$-coordinates equals $1+\pi^p L\bmod\pi^{p+1}$, where $L=\sum_i\kappa_i(b_i^p-r_i^{p-1}b_i)$ and $\kappa_i=U/(Y_iT_i)$. This follows by expanding the curve equation and using $p/\pi^{p-1}\equiv-1$. Detection forces $\operatorname{Tr}(L)=0$, since the coefficient of a $p$th power at this depth has the form $b^p-b$.

For the opposite conclusion put $H_1(x)=(1-(1+4dx)^{20})/(2x)$. We have $Y_i(\kappa_i^{1/p}-r_i^{p-1}\kappa_i)=H_1(r_i)$ by $r_i\kappa_i^{1/p}=(Z_i-1)/(2Z_i)$. Trace is Frobenius invariant. Pairing the differential vector with the coefficients of the degree-19 polynomial $H_1$ thus gives $\operatorname{Tr}(L)=c_0\operatorname{Tr}((W/Y_0)(xH_1)'(1))$. In characteristic 41, $(xH_1)'=d(1+4dx)^{19}$, and $(Y_0^{1/p})^2=1+4d$. Therefore
$$\operatorname{Tr}(L)=c_0\operatorname{Tr}\bigl(W(U/Y_0^3)^{1/p}\bigr)=31c_0\ne0.$$
The traced element has power-basis coefficients $(28,14,25,30,40,18)$ and the traces of the six basis powers are $(6,-1,11,-4,31,-16)$. The contradiction proves the claim.

## Reproduction

```sh
python3 residues.py
gp -qf auxiliary.gp
gp -qf -s 200M certificate.gp
lean Identities.lean
```

The Python script enumerates all 163 projective finite residues of the extraneous class, counts points on each quadratic-field elliptic model, tests both 41-adic entry charts by Frobenius, and computes the trace via the Frobenius conjugate $W^{41}U/Y_0^3$. PARI 2.19.1 constructs the models from the original cyclotomic formulas, performs the class-group computation, and Newton-lifts forty points to verify their actual Kummer product at depth 42. The ring modulo $41^2$ retains precision through depth 79, and $\pi^{41}\equiv-41\pi\pmod{\pi^{42}}$. The Lean 4.33.1 lemmas check the normalization and finite scalar identities. The global descent and formal Picard argument are written proofs for review.
