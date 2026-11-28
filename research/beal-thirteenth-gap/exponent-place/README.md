# Comparing the Frey curves at the output exponent in (13,13,p)

Deldor14 · 28 November 2026 · Written proof for mathematical review

Consider nonzero integers $a,b,c$ with $a^{13}+b^{13}=c^p$ and $\gcd(a,b,c)=1$, for a prime $p\ge5$, $p\ne13$.

1. The set of rational primes $p$ for which such a solution can have **$p\mid a+b$ has natural density zero among primes**. This includes split and inert rational primes in $\mathbb Q(\sqrt{13})$.
2. For **every one of the 666 primes $5\le p\le5000$, $p\ne13$**, a hypothetical solution satisfies $p^2\mid ab$, $p\nmid a+b$, and $a+b\zeta_{13}$ is a global $p$th power in $\mathbb Z[\zeta_{13}]$.

The density assertion concerns a branch of the equation. In the finite interval the divisibility and the pure power are necessary conditions. The proofs are unconditional. The finite result needs no hypothesis on the class group of a field of conductor $13p$.

## A local comparison at the varying prime

Write $K=\mathbb Q(\sqrt{13})$ and $E_-,E_0,E_+$ for the Frey curves $E_{1,-1},E_{1,0},E_{1,1}$ over $K$. Best–Dahmen–Freitas Theorem 1.2 implies $13\nmid a+b$, and their Proposition 2.2 and §4.3 give $E_{a,b}[p]\simeq E_j[p]$ over $K$ for a single $j\in\{0,+\}$. Their representations are irreducible, so an isomorphism after semisimplification suffices. [Best–Dahmen–Freitas](https://arxiv.org/html/2510.12092v1#S4.SS3)

Suppose $p\mid a+b$. At every place $v\mid p$ in $K$, $E_{a,b}$ has good reduction and its reduction is isomorphic to that of $E_-$. Indeed $b=-a$ in the residue field, $a$ is a unit, and the short coefficients are homogeneous of degrees four and six. The reductions of $E_-,E_0,E_+$ are smooth at every prime above any $p\ge5$, $p\ne13$: in the cyclotomic factorization of the discriminant the coordinate factors for $(1,-1),(1,0),(1,1)$ have prime divisors only above 13 or are units. [Billerey–Chen–Dieulefait–Freitas, §7.1](https://lmbp.uca.fr/~billerey/Research/Published/BCDF19_MultiFrey.pdf)

Here $K_v/\mathbb Q_p$ is unramified. Raynaud's full faithfulness for finite flat commutative $p$-group schemes over a DVR with absolute ramification index $e<p-1$ extends the generic isomorphism of the finite flat $p$-torsion of the two elliptic schemes, and its inverse, to the integral models. Thus the special-fibre $p$-torsion group schemes are isomorphic over the residue field $k_v$. In the ordinary case the geometric points form a line over $\mathbb F_p$, on which the $|k_v|$-power Frobenius acts invertibly by the reduction of its integral trace: the relation $F^2-a_v F+|k_v|=0$ on the line gives this identity. In the supersingular case both curves have zero geometric $p$-torsion and $a_v\equiv0\pmod p$. Consequently
$$ a_v(E_-)\equiv a_v(E_j)\pmod p \quad\text{at every }v\mid p,$$
for the same choice of $j$. This comparison uses finite flat group schemes at the residue characteristic. [Conrad, *Finite group schemes over bases with low ramification*](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0010437X99000767)

## Geometric independence of the six fixed curves

Let $h^2=h+3$ and $K=\mathbb Q(h)$. In the cyclotomic presentation $h=1+\sum_{j=1,3,4}(z^j+z^{-j})$, $z=\zeta_{13}$. The short coefficients of the three curves in order are
```
(-2106+702h, 42120-16497h), (-189+27h, 837-270h), (-270-162h, -1188-783h).
```
These follow directly from the Frey model in the reference. Consider the six curves in the order $E_-, E_-^s,E_0,E_0^s,E_+,E_+^s$, where $s$ is the nonidentity automorphism of $K$. At each of the four following split rational primes choose the embedding sending $h$ to the smaller integer root modulo that prime. Direct point counting gives Frobenius traces as follows.

| prime | six traces |
|---:|---|
| 79 | 0, 0, −8, 8, 16, −8 |
| 131 | −12, 0, 12, −8, 12, 0 |
| 311 | −4, 24, 12, 0, −4, −24 |
| 599 | 40, 0, 16, 24, 0, 16 |

For each pair of columns some row has exactly one zero. At these prime-field places the zero is supersingular and the nonzero trace is ordinary by the Hasse bound. Thus the six curves are pairwise non-isogenous over $\overline K$: an isogeny over a finite extension would preserve the $p$-rank after good reduction. They are all non-CM, since a CM elliptic curve and its conjugate have the same geometric CM field and hence are geometrically isogenous.

## Natural density for rational primes

Fix an auxiliary prime $\ell$, say 7. Apply Lombardo's open image theorem to the six curves over $K$. Their joint $\ell$-adic image is open in the group of six integral invertible $2\times2$ matrices of common determinant. The common determinant is the cyclotomic character $\chi_\ell$. [Lombardo, *An explicit open image theorem for products of elliptic curves*](https://arxiv.org/abs/1501.04600)

For each of the three original Tate modules use its induced representation from $G_K$ to $G_{\mathbb Q}$, with two blocks restricting to that curve and its conjugate. Retain also the quadratic character of $K$ and $\chi_\ell$. For any element $g$ of this compact image, $g^2$ preserves every block. At a rational prime of good reduction away from $\ell$, take arithmetic Frobenius $g$. The trace of $g^2$ on one block is the elliptic trace over $\mathbb F_{p^2}$. For split $p$ this is the trace on extending the prime-field model to degree two. For inert $p$ it is the trace at the place of $K$ already.

If the necessary local comparison holds, the traces on the appropriate blocks for $E_-$ and $E_j$ agree modulo $p$ after passing to $\mathbb F_{p^2}$. For split primes this also follows from $a_{p^2}=a_p^2-2p$. Each trace has absolute value at most $2p$. The difference is therefore $m\chi_\ell(g)$ for some integer $-4\le m\le4$. The exceptional Frobenius elements belong to the finite union of the corresponding trace-equality loci, taking the two simultaneous choices of conjugate blocks and both choices of $j$.

Each locus has Haar measure zero. On the subgroup over $K$ the squared-block trace is $\operatorname{tr}(A^2)$; on the other coset the square on one block has the form of a product of the two interchange maps between that curve's blocks. On either coset, fixing the determinant and allowing variation in just one $\mathrm{SL}_2$ factor for $E_-$ leaves $E_j$ and the character fixed. In the first case $\operatorname{tr}(A^2)=\operatorname{tr}(A)^2-2\det A$ is nonconstant under such variation. In the second, the function becomes the trace of an invertible matrix times the variable matrix, also nonconstant. These statements hold on every open neighborhood by openness over $K$ and Zariski density of open subsets of $\mathrm{SL}_2(\mathbb Z_\ell)$. Thus no displayed analytic equation vanishes on an open set. A proper polynomial zero locus in these smooth $\ell$-adic charts has Haar measure zero. The finite union, including conjugates, is closed and invariant under conjugacy. Applying finite Chebotarev to congruence neighborhoods and letting their Haar measures decrease to zero gives upper natural density zero. This proves assertion 1.

## All exponents through 5000

PARI point counts and a separate Hasse-coefficient computation agree on the necessary comparison: the *only* prime in the specified range where one model $E_j$ matches $E_-$ at every $v\mid p$ is **3067**. At its two split places the triples are $(28,60,28)$ and $(64,-8,64)$. We treat this exception below.

For an independent mod-$p$ trace calculation on $y^2=x^3+Ax+B$, use $H=[X^{p-1}](X^3+AX+B)^{(p-1)/2}$. The trace modulo $p$ is $N_{k_v/\mathbb F_p}(H)$. Indeed the point count reduces to the power sum of $(X^3+AX+B)^{(|k_v|-1)/2}$; only the coefficient in degree $|k_v|-1$ contributes. Its base-$p$ factorization forces the index $p-1$ in every Frobenius factor, since its degree is $3(p-1)/2<2p-1$. The Python verifier computes the coefficient by multinomial expansion.

Set $D=a+b$ and $L=\mathbb Q(z)$. In the cyclotomic descent $D=v^p$, $a+bz=\epsilon\beta^p$ and $N(a+bz)$ is a rational $p$th power. The unit $\epsilon$ is real up to a root of unity, since $\epsilon/\bar\epsilon$ is a root of unity reducing to 1 at $1-z$. All these roots are $p$th powers. If $p\nmid D$, put $t=a/D$ and $A=t+(1-t)z$. In the product algebra modulo $p^2$, with Frobenius $\sigma(z)=z^p$, we have
$$ A^p\sigma(\bar A)-\bar A^p\sigma(A)=0\pmod{p^2}.$$
In particular the identity remains necessary at a component where $A$ is a nonunit. In fact write $A=\epsilon B^p$ with $B$ integral at $p$; use $(B^p)^p\equiv\sigma(B)^p$ and its conjugate, and $\epsilon^p\sigma(\bar\epsilon)=\bar\epsilon^p\sigma(\epsilon)$ from the root-of-unity ratio. The norm $t^{13}+(1-t)^{13}$ must either vanish modulo $p^2$ or have $(p-1)$st power 1 there.

Write $t=t_0+pk$. The first two $p$th powers in the cross product depend only on $t_0$. After division by $p$ the equation is linear in $k$, with slope $z^p-z^{-p}\ne0$ modulo $p$. For every $t_0$ the verifier solves on one nonzero coefficient and tests the whole vector; it then applies the rational norm test. For all 666 primes the angle test has three residues, and the norm test leaves exactly 0 and 1 except at **1093 and 3511**, where it also leaves $1/2\bmod p^2$. This computation includes primes splitting completely in $L$. [Projective sieve and cyclotomic descent](https://github.com/Deldor14/open-math-agents/tree/27ac4a9c87fd3a0cd7e67a0a494dbbd6222f66ce/research/beal-thirteenth-gap/eighteen-signatures)

To handle the unit information it suffices to work in the fixed degree-six real subfield. For $w=z+z^{-1}$ use the units
$$w,\quad w^2-1,\quad w^3-2w,\quad w^4-3w^2+1,\quad w^5-4w^3+3w.$$
The unconditional BNF certificate and determinant one in a fundamental unit basis verify these generate modulo sign. The map on units $u\mapsto (u^{p^{12}-1}-1)/p\bmod p$ is additive under multiplication, and vanishes on $p$th powers. The five columns in the cyclotomic power basis have rank five for all tested $p$ except 151 and 241, where each kernel has dimension one. Thus at each rank-five prime a global unit whose local class is trivial modulo $p^2$ is a global $p$th power. Roots of unity do not affect this statement.

At 3067 the branch $p\mid D$ would give $a+bz\equiv a(1-z)\bmod p^2$ and $13a^{12}$ a $p$th power modulo $p^2$. Consequently $a/13^k$ is a local $p$th power for $12k\equiv-1\bmod p$. The rank-five condition gives the global unit class $\mu=(13/(1-z)^{12})^k$. At $q=12269$, order six modulo 13, no finite normalized $t=a/D\bmod q$ satisfies the power test for $(t+(1-t)z)/\mu$ in the full residue algebra. Thus $q\mid D$ and $E_{a,b}$ reduces to $E_-$. Over the chosen degree-six residue field the traces of the three models are $-3686387808582,2002032350138,-3392560309318$. The first differs from both others modulo 3067, ruling out this branch.

At 1093 and 3511, $2^{p-1}\equiv1\bmod p^2$. The additional residue $t=1/2$ makes $A$ locally $(1+z)/2$ modulo $p^2$. Here 2 is a local $p$th power, so rank five forces the global unit class $1+z$. Use $q=4373$ and $77243$, respectively, of residue degrees four and six in $L$. Testing every finite $t$ eliminates this unit. If $q\mid D$, the $(q^f-1)/p$ power of $(1-z)/(1+z)$ is nonscalar, which no rational scalar can correct. This eliminates the two last finite exceptions. Thus $p\nmid D$ and $p^2\mid ab$ throughout the interval.

Finally, in the surviving classes $A\equiv1$ or $z$ modulo $p^2$, so $\epsilon$ belongs to the global unit kernel computed above. For 151 and 241, respectively, a spanning vector in the displayed unit basis is $(32,119,150,118,1)$ or $(1,240,240,1,1)$. Call the corresponding unit $u$. At an auxiliary $q$, write $f=\operatorname{ord}_{13}(q)>1$ and $m=(q^f-1)/p$. For each possible exponent $j\bmod p$, the finite chart requires $(t+(1-t)z)^m=u^{jm}$ for some rational $t\bmod q$. The infinite chart requires $((1-z)/u^j)^m$ to be scalar, and equal to 1 if $p\nmid q-1$. For 151, $q=269$ leaves only $j=0$. For 241, $q=1447$ leaves $0,128,201$, and intersecting with $q=4337$ leaves only 0. Thus $a+bz$ is a global $p$th power in all 666 cases. This proves assertion 2.

## Reproduction and scope

```sh
gp -qf -s 256M verify.gp
python3 hasse.py
lean Witness.lean
```

The calculations were run with PARI/GP 2.19.1 and Lean 4.33.1 with Mathlib. Python uses the standard library. It independently compares the traces at the exponent in characteristic $p$ and counts points at the four good split primes for all fifteen geometric pairs. Lean checks the separation of all pairs from the displayed table, the slope identity and the squared-trace identity. The finite-flat, Galois-image and density arguments are written proofs for mathematical review.
