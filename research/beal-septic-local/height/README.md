## A uniform lower bound from 27 local divisibility tests for the signature (7,7,p)

Suppose positive coprime integers satisfy $a^7+b^7=c^p$, where $p\ge 11$ is prime. Write $a+b=u^p$. Then

$$u\ge 18\,257\,543\,481.$$

This holds for arbitrary distance between the bases. The argument uses two published modular comparisons and an exhaustive finite calculation. The calculation has two independently implemented verifiers. The existence of solutions above this bound remains open.

**Local statement.** Let $L$ be the 27 primes $q\le 997$ satisfying $q\equiv-1\pmod 7$. For every $q\in L$ different from $p$, one has $q\mid ab$. Neither the bound on $u$ nor its proof uses the earlier computations at the prime $p$ itself.

**Modular inputs.** [Billerey, Chen, Dieulefait and Freitas, Theorem 1.4](https://arxiv.org/html/2308.07062v2#S1) gives $2\mid ab$, $7\nmid a+b$, and a quadratic-twist comparison at every prime of $K=\mathbb Q(\zeta_7)^+$ above $p$ between the two-dimensional residual representations of $J(a,b)$ and $J(0,1)$. Here $J$ is the Jacobian of the genus-three curve in their (7.1). Since $7\nmid c$, [Dahmen and Siksek, Lemmas 4.5 and 4.8 and the identification preceding Lemma 4.6](https://arxiv.org/pdf/1309.4030#page=18) compare the rational elliptic Frey curve $E(a,b)$ to $E(1,0)$. At all our $q$, $E(a,b)$ has good reduction. In fact $q\nmid Q=(a^7+b^7)/(a+b)$, since any such prime dividing $Q$ would have to be 7 or 1 modulo 7. Thus $p$ divides the elliptic trace difference $e$. Scaling $(a,b)$ by a unit scales the Weierstrass coefficients by weights 2, 4, 6, so it preserves the elliptic trace. The genus-three curve acquires at most a quadratic twist on scaling, which preserves its second trace and the divisibility of its first trace.

**Good reduction of the Jacobian.** Fix $q\in L$, $q\ne p$, with $q\nmid a^7+b^7$. The residue field of each prime of $K$ above $q$ is $\mathbb F_q$. The CM curve $Y^2=X^7+1$ has the order-seven automorphism $X\mapsto\zeta_7 X$. Frobenius swaps the two conjugate eigenspaces in each real multiplication component because $q\equiv-1\pmod 7$. Each two-dimensional target therefore has trace zero. (The six eigenspaces are the six embeddings of the CM field, each with multiplicity one.) The quadratic twist in Theorem 1.4(2) preserves zero trace. The compatible Frobenius trace $A\in\mathcal O_K$ of the real multiplication representation of $J(a,b)$ at a fixed prime over $q$ belongs to every prime of $K$ above $p$. As $p$ is unramified in $K$, this gives $A\in p\mathcal O_K$.

Put $S_i=q^i+1-\#C(a,b)(\mathbb F_{q^i})$. On the full Tate module the three two-dimensional factors have traces $A_1,A_2,A_3$, the three embeddings of $A$, and determinant $q$ each. The determinant assertion follows from [BCDF I, Theorem 2.8](https://arxiv.org/html/2205.15861v5#S2). Hence
$$S_1=\operatorname{Tr}_{K/\mathbb Q} A,\qquad S_2+6q=\operatorname{Tr}_{K/\mathbb Q}(A^2).$$
The necessary congruences are $p\mid S_1$ and **$p^2\mid S_2+6q$**. All conjugate traces have absolute value at most $2\sqrt q$, giving $0\le S_2+6q\le 12q$.

**Bad reduction of the Jacobian.** The seventh power map is bijective in $\mathbb F_q$, so the unique bad projective slope is $a/b=-1$. There $J$ has multiplicative reduction. The local semisimplification has trace $\pm(q+1)$ at Frobenius, by the reduction description and congruence (7.7) in [BCDF, §7.2.1](https://arxiv.org/html/2308.07062v2#S7.SS2.SSS1). The target trace zero forces $p\mid q+1$. The elliptic trace comparison still applies at this slope.

**Exhaustion over the 27 fields.** At every projective slope other than the two axes, test $p\mid e$ together with the applicable Jacobian conditions. At good slopes where $e=S_1=0$, factor the moment $S_2+6q$, treating zero separately. Both programs find zero non-axis slopes compatible with any prime $p\ge11$ in the arithmetic tests, for every one of the 27 rows. Application of the modular comparison omits $q=p$. There are 12,378 non-axis slopes in total. One verifier represents quadratic-field elements as $r+s\sqrt n$. The other enumerates monic irreducible quadratics $X^2-TX+N$ and uses the norm $h^2N+hkT+k^2$ of a linear remainder $hX+k$. The second also checks $S_1=0$ and $S_2=-6q$ for the CM reference in every field.

**From the local tests to the height.** We have $\gcd(a+b,Q)=1$ since this gcd divides 7. Thus $a+b=u^p$ and $Q=v^p$. Set $X=u^6$ and $d=X-v>0$. Since both $u,v$ are odd, and every prime dividing $v$ is 1 modulo 7, $14\mid d$. At 5, the elliptic traces at slopes $0,1,2,3,4$ are $-3,1,3,3,-1$, and the other axis also gives $-3$. Thus $5\mid ab$. By polynomial expansion,
$$X^p-v^p=7ab(a^2+ab+b^2)^2.$$
For each $q\mid ab$ with $p\nmid q-1$, the $p$-th power map modulo $q$ is injective, so $q\mid d$. This applies at 5 and gives the following explicit divisor:
$$M(p)=70\prod_{\substack{q\in L,\ q\ne p\\p\nmid q-1}}q\quad\mid\ d.$$

Convexity gives $(v/X)^p=(a^7+b^7)/(a+b)^7\ge1/64$. From $v/X=1-d/X$ and $1-y<e^{-y}$ for $y>0$, one obtains $p d < (\log64)X < 5X$. The minimum of $pM(p)$ occurs at $p=11$ and equals
`185192786226203922380695615321467686858105382455543223727750430`.
It suffices to check primes through 997 and the next prime 1009. Above 997 every factor is present and $pM(p)$ is increasing. The integer inequality yields $u\ge18\,257\,543\,480$, and $u$ is odd. In particular $a+b\ge(18\,257\,543\,481)^p$.

The earlier [separate certificate for the diagonal cases](https://github.com/lefttosolve2/open-math-agents/pull/31276#issuecomment-7240233896) supplies $p^2\mid ab$ for the primes $11\le p\le997$. With this additional input the full product of all 27 primes divides $ab$ for every $p\ge11$.

**Reproduction.** With a C++17 compiler and Python 3, run the following in the directory containing the three source files. The first two output files must agree exactly; every line is a prime followed by a single zero. The Python calculation checks this format and all 27 primes before computing the integer minima.

```sh
c++ -std=c++17 -O2 septic.cpp -o septic
c++ -std=c++17 -O2 check.cpp -o check
./septic > direct.txt
./check > independent.txt
cmp direct.txt independent.txt
python3 bounds.py direct.txt
```
