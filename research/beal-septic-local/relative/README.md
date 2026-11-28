# A local obstruction for primitive sums of two seventh powers

Suppose that positive coprime integers satisfy $a^7+b^7=C^N$, with $N\ge 2$. For every prime $11\le p\le 20000$ dividing $N$, **$p^{1+v_p(N)}$ divides one of $a,b$**. The bound is on the prime divisor of the exponent. The bases and the exponent $N$ can be arbitrarily large.

## Cyclotomic test

Write $c=C^{N/p}$, $D=a+b$, and $Q=(a^7+b^7)/D$. Theorem 1.4(1) of Billerey–Chen–Dieulefait–Freitas gives $7\nmid D$. Since $\gcd(D,Q)=1$, there are positive coprime integers $u,v$ with $D=u^N$, $Q=v^N$. We use the written result $p\nmid c$ in the accompanying exponent note. That dependency is what allows the following enumeration to omit the residue classes $x^7=-1$. [BCDF II](https://arxiv.org/html/2308.07062v2#S1) · [Proof at the exponent prime](../exponent/README.md)

Put $L=\mathbb Q(\zeta)$, $\zeta=\zeta_7$. The seven ideals $(a+b\zeta^j)$ are pairwise coprime. A common prime would divide $b(\zeta^i-\zeta^j)$, forcing it over 7 by primitivity, contrary to $7\nmid D$. They multiply to $(c)^p$. Since $L$ has class number one, $a+b\zeta=\epsilon\gamma^p$ for a unit $\epsilon$ and an algebraic integer $\gamma$. The quotient $\epsilon/\bar\epsilon$ is a unit of absolute value one at every embedding and hence a root of unity. All roots of unity in $L$ have order dividing 14. Thus $(a+b\zeta)/(a+b\zeta^{-1})$ is a $p$-th power in $L$. [Dahmen–Siksek, §4.1](https://arxiv.org/pdf/1309.4030#page=15)

Suppose $p\nmid ab$. Then $t=a/b\in\mathbb Z_p^\times$ and $x=t\bmod p$ satisfies $x^7\ne-1$. The above quotient is a unit at every prime over $p$. At this unramified prime the automorphism $\sigma(\zeta)=\zeta^p$ agrees modulo $p$ with the $p$-power map. Applying that congruence to a local $p$-th root and raising to the $p$-th power gives $\sigma(R)=R^p\bmod p^2$ for the quotient $R$. Consequently the following difference vanishes modulo $(p^2,\Phi_7(Z))$:

$$ (t+Z)^p(t+Z^{-p})-(t+Z^{-1})^p(t+Z^p). $$

In the cyclic model $Z^7=1$ its constant coefficient is zero, and its coefficients at opposite indices are negatives. A cyclic representative of degree at most six which is zero modulo $\Phi_7$ has all coefficients equal. It suffices to check indices $l=1,2,3$. Put $P_j=[Z^j](x+Z)^p$ in the cyclic model with modulus $p^2$. Writing $t=x+hp$ leaves the $P_j$ unchanged, and the three tests are

$$ (x+hp)(P_l-P_{-l})+P_{p+l}-P_{p-l}=0\pmod{p^2}, $$

where subscripts are modulo 7. Exactly one of $P_l-P_{-l}$ is $\pm1$ modulo $p$, so its equation uniquely fixes $h$. The other two equations are independent of $h$. The C++ program uses this form.

## Independent test over the prime field

Set $b_j=(-1)^{j-1}/j\in\mathbb F_p$ and $V_l(X)=\sum_{j=1}^{p-1}(\mathbf1_{j\equiv l}-\mathbf1_{j\equiv-l})b_jX^j$, where the indicators use modulus 7. For each of the two indices $1\le l\le3$ with $l\not\equiv\pm p\pmod 7$, the equation reduces to

$$ V_l(x)=x^2V_l(1/x). $$

Indeed $\binom pj/p=b_j\bmod p$ and $b_j=b_{p-j}$. The first coefficient difference, multiplied by $x$ and divided by $p$, contributes $x^{p+1}V_l(1/x)$. In the shifted difference the interior terms give $-V_l(x)$ on replacing $j$ by $p-j$. The endpoint terms cancel with the corresponding terms from the first difference (at these two indices neither endpoint contributes). This proves the displayed criterion. The Python program tests it over every eligible residue using exact integer convolution, with $ij=\binom{i+j}{2}-\binom i2-\binom j2$. Its radix exceeds the largest possible convolution coefficient.

## Remaining residue and lifting

For every one of the 2,258 primes, the independent prime-field computation returns exactly $x=1$. The cyclic computation returns one class as well. These enumerations cover 21,164,396 nonzero residues with $x^7\ne-1$ across all primes. Since $(t^7+1)/(t+1)^7=Q/D^6$ is a rational $p$-th power unit, its $(p-1)$-st power is one modulo $p^2$. Its derivative vanishes at $t=1$, where its value is $2^{-6}$. Thus $2^{p-1}=1\bmod p^2$ (raise $2^{p-1}=1+kp$ to the sixth power). Only 1093 and 3511 satisfy this in the tested range.

At $7\nmid c$, Lemmata 4.5 and 4.8 of Dahmen–Siksek give equality modulo $p$ of the Frey elliptic trace with the trace of $E_{1,0}$ at good reduction. Lemma 4.5 explicitly permits the auxiliary prime to equal the exponent for a rational newform. At slope 1, $E_{a,b}$ reduces to a curve isomorphic to $E_{1,1}$ by scaling $X$ by $b^2$ and $Y$ by $b^3$. The models on the right are $Y^2=X^3-X^2-2X+1$ and $Y^2=X^3-7X-7$, respectively. Their trace pairs are $(38,-58)$ at 1093 and $(-43,69)$ at 3511. Both contradict the congruence. Hence $p\mid ab$. [Dahmen–Siksek, §§4.1–4.2](https://arxiv.org/pdf/1309.4030#page=16)

Finally $D^6-Q=7ab(a^2+ab+b^2)^2$. Primitivity and $p\mid ab$ imply that the right-hand side has valuation $v_p(ab)$. Write $N=mp^e$ with $p\nmid m$. Both $u,v$ are units at $p$ and $u^{6m}\equiv v^m\pmod p$ since Frobenius is injective. The odd-prime lifting-the-exponent formula gives $v_p(ab)=v_p(u^{6m}-v^m)+e\ge e+1$. The difference is nonzero by positivity and the displayed identity. Since $a$ and $b$ are coprime, the full power of $p$ divides one base.

## Reproduction

Use Python 3 and a C++17 compiler. Run in this directory with Python assertions enabled.

```sh
c++ -O3 -std=c++17 check.cpp -o check
./check 20000 > my-ring.txt
python3 fourier.py 20000 > my-fourier.txt
python3 verify.py 20000 my-ring.txt my-fourier.txt
```

The supplied tables are `ring.txt` (prime, eligible residues, relative survivors, rational survivors, elliptic survivors) and `fourier.txt` (prime followed by each surviving relative residue). The verifier checks the prime coverage, the size of each residue set, the survivors, the base-two exceptions, and both trace comparisons by Euler's criterion. This is a written argument with reproducible computations. Solutions on the surviving axes remain open.
