# A primitive sum of two seventh powers requires a prime factor of a base above 100,000

Suppose $a,b,C$ are positive coprime bases and $a^7+b^7=C^N$ for an integer $N\ge2$. **Some prime divisor of $ab$ exceeds 100,000.** Equivalently, the equation has no primitive positive solution with both $a$ and $b$ 100,000-smooth. There is no upper bound on $a$, $b$, $C$ or $N$. The argument starts with a necessary condition on the prime divisors of the *larger* base which works for every prime exponent, then certifies the finite list to which smoothness would restrict the exponent.

## A necessary prime divisor of the larger base

Fix a prime $p\ge11$ dividing $N$. Write $D=a+b=u^p$ and $Q=(a^7+b^7)/D=v^p$. Indeed $7\nmid D$ by BCDF II, Theorem 1.4(1), and $D,Q$ are coprime. The same theorem gives $2\mid ab$, hence $D$ is odd and $u\ge3$. Put $M=\max(a,b)$. There is a prime $r\mid M$, $r\ne7,p$, such that $p\mid r^{f_r}-1$, where $f_r=\operatorname{ord}_7(r)$. [BCDF II](https://arxiv.org/html/2308.07062v2#S1)

To see this, put $L=\mathbb Q(\zeta_7)$, $A=a+b\zeta_7$, and $R=A/\overline A$. As in Dahmen–Siksek §4.1, the factorization gives $A=\epsilon\gamma^p$ for an algebraic integer $\gamma$ and a unit $\epsilon$. Its quotient by its conjugate is a $p$-th power: $\epsilon/\bar\epsilon$ is a root of unity of order dividing 14. Take $\rho\in L$ with $\rho^p=R$. Every conjugate of $\rho$ has absolute value one. Moreover $v\rho$ is an algebraic integer because $(v\rho)^p=QA/\bar A$ is integral, $\bar A$ being a factor of $Q$ in $\mathcal O_L$. [Dahmen–Siksek](https://arxiv.org/pdf/1309.4030#page=15)

Choose $\lambda=1$ when $M=b$, and choose the unique seventh root $\lambda$ with $\lambda^p=\zeta_7^2$ when $M=a$. Let $r^h\Vert M$. Both $A,\bar A$ and $v$ are units above $r$. If $M=b$, then $R-1=b(\zeta_7-\zeta_7^{-1})/\bar A$. If $M=a$, then $R-\zeta_7^2=a(1-\zeta_7^2)/\bar A$. Thus $(\rho/\lambda)^p=1\bmod r^h$ in the local rings above $r$.

If $r\ne p,7$ and $p\nmid r^{f_r}-1$, the residue fields have cardinality $r^{f_r}$ and contain no nontrivial $p$-th root of unity. The residue of $\rho/\lambda$ is therefore one. The other factor in $X^p-1=(X-1)(1+\cdots+X^{p-1})$ reduces to the unit $p$; hence $\rho/\lambda=1\bmod r^h$. The same proof works for $r=7$, using residue field $\mathbb F_7$, including its ramification. At $r=p$ the residue also equals one and the extension is unramified. The binomial expansion for $X=1+s$, $v_p(s)\ge1$, gives $v_p(X^p-1)=v_p(X-1)+1$ unless $X=1$, where the congruence is automatic. We obtain $\rho/\lambda=1\bmod p^{\max(0,h-1)}$.

More quantitatively let $G$ be the product of the prime powers of $M$ covered by these congruences, dropping one factor $p$ if $p\mid M$. The nonzero algebraic integer $v(\rho-\lambda)$ is divisible by $G$ in $\mathcal O_L$. Its nonvanishing follows from $a,b>0$ and the two exact difference formulas. Its six conjugates have absolute value at most $2v$. Taking absolute norms gives $G\le 2v<2u^6$, since $Q<D^6$. If every prime factor of $M$ were covered, then $M\le pG<2pu^6$. But $M\ge u^p/2$, giving $u^{p-6}<4p$, impossible for $p\ge11$ and $u\ge3$. This proves the stated necessary condition. The elementary size inequality is also checked in Lean.

## The finite certificate under smoothness

If $ab$ is 100,000-smooth, some prime $r\le100000$, $r\ne7$, must satisfy the preceding condition. The complete union of prime divisors $p\ge11$ of $r^{f_r}-1$ has 9,547 elements, with maximum 9,984,705,853. One computation uses the cyclotomic factorization for $f_r=1,2,3,6$; a separate PARI/GP computation factors the integers directly and returns the identical list.

For each listed $p$, `certificates.txt` gives a prime $q>100000$ with $q\equiv1\pmod{14p}$ and proves $q\mid ab$. On the supposition of smoothness both bases are units at $q$. At $q\nmid D$, consider the six embeddings $\zeta_7\mapsto z^j$ in $\mathbb F_q$. In each opposite pair of nonzero factors the ratio is a $p$-th power by the preceding relative factorization; also $Q/D^6$ is a $p$-th power where nonzero. For $p\le20000$ we can impose the stronger condition that every nonzero $(a+bz^j)/D$ is a $p$-th power by the [pure cyclotomic descent](../units/README.md). The checkers enumerate the $m=(q-1)/p$ possible values of one opposite ratio and both of its possible zero-factor exceptions. They then evaluate the remaining conditions. This leaves only $a=0$ or $b=0$ modulo $q$ among slopes with $q\nmid D$.

At $q\mid D$, the Frey elliptic curve reduces to $E_{-1,1}$ up to a change of coordinates because the septic cofactor is $7b^6\bmod q$, nonzero. Its trace must agree modulo $p$ with $E_{1,0}$ by Dahmen–Siksek Lemmata 4.5 and 4.8. The two models are $Y^2=X^3-4X^2-11X+43$ and $Y^2=X^3-X^2-2X+1$, respectively. The certificates contradict the congruence in one of three ways. [Dahmen–Siksek, §4.2](https://arxiv.org/pdf/1309.4030#page=18)

| Type | Exponents | Check |
|---|---:|---|
| `table` | 1,513 | The earlier [split-prime certificates](../units/auxiliary.txt) directly give $q>100000$ dividing $ab$. |
| `trace` | 265 | Two distinct residues modulo $p$ are certified by exact prime-field point counts. |
| `three` | 7,769 | One group of rational points has order divisible by 3, and the other does not. As $16q<p^2$, the Hasse bound gives an absolute trace difference smaller than $p$. The distinct integer traces are therefore distinct modulo $p$. |

For `three`, rational 3-torsion is equivalent to a common root in $\mathbb F_q$ of the 3-division polynomial with a nonzero square ordinate on the curve. The independent verifier checks this with two polynomial greatest common divisors, using $X^q-X$ and Euler's square criterion. The search instead finds all roots of the quartic using PARI/GP. For new rows with $p^2>q$, primality of $q$ is proved by an element whose order has a factor $p$ modulo every prime divisor of $q$, which forces every prime divisor to exceed $\sqrt q$. Smaller $q$ are checked by trial division. The largest auxiliary prime is 9,981,460,126,051. Thus every possible exponent forces a prime divisor of $ab$ larger than the assumed bound.

If $N$ has a prime factor $2,3,5$ or $7$, the corresponding primitive equation is already excluded by Darmon–Merel, Dahmen–Siksek, or Fermat's last theorem, respectively. These cover all other possible exponents. [BCDF II, §2](https://arxiv.org/html/2308.07062v2#S2) · [Dahmen–Siksek, Theorem 2](https://arxiv.org/abs/1309.4030)

## Reproduction

Run with Python 3.9+ and assertions enabled. The `units` directory one level up is required for the inherited certificates. From this directory use the following commands.

```sh
python3 ../units/check_aux.py ../units/auxiliary.txt 20000
python3 verify.py
# Optional regeneration
python3 resonance.py 100000 > new-exponents.txt
gp -fq prime_factors.gp > independent.txt
cmp new-exponents.txt independent.txt
python3 search.py 100000 new-exponents.txt gp ../units/auxiliary.txt > new-rows.txt
cmp new-rows.txt certificates.txt
```

`Archimedean.lean` compiles against Mathlib on Lean 4.33.1 and checks the two size inequalities used above. The arithmetic and the finite certificate are a written proof for review. The general septic equation with a larger prime divisor remains outside this exclusion.
