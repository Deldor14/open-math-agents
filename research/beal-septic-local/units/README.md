# Pure cyclotomic factors in the septic Fermat equation

Let $a,b,C$ be positive, $\gcd(a,b)=1$, and $a^7+b^7=C^N$. For each prime $11\le p\le20000$ dividing $N$ there is an algebraic integer $\beta\in\mathbb Z[\zeta_7]$ with

$$a+b\zeta_7=\beta^p.$$

The table gives a further explicit prime $q=q(p)$ dividing $ab$. The denominator-free computation below then proves $p^{1+v_p(N)}\mid ab$ independently of any result about the Jacobian at the prime $p$. Outside $p=61,5419,12703$, the conclusion about the cyclotomic factor also holds with the full exponent $p^{v_p(N)}$. All statements concern unrestricted positive bases.

## An auxiliary prime certifies the global unit class

Let $D=a+b=u^N$, $Q=(a^7+b^7)/D=v^N$. This splitting follows by coprimality and $7\nmid D$, the latter from BCDF II, Thm 1.4(1). With $L=\mathbb Q(\zeta_7)$ and $\zeta=\zeta_7$, the seven factors $a+b\zeta^i$ are pairwise coprime. Write $U=1+\zeta$, $V=1+\zeta^2$. The class number and unit generators of $L$ give $a+b\zeta=U^r V^s\gamma^p$, since torsion has order prime to $p$. The quotient by the complex conjugate is a $p$-th power: the quotient of a unit and its conjugate is a root of unity. Dahmen–Siksek give the global unit conclusion for primes below 100 in Proposition 4.1. Here we extend their unramified branch through 20000 and give one explicit auxiliary divisor for each prime. [BCDF II](https://arxiv.org/html/2308.07062v2#S1) · [Dahmen–Siksek, §§4.1–4.3](https://arxiv.org/pdf/1309.4030#page=15)

Fix a certified prime $q\equiv1\pmod{14p}$, set $m=(q-1)/p$ and enumerate the six seventh roots of order seven, $z_j=z^j\in\mathbb F_q$. If $q\nmid b$, write $t=a/b\bmod q$. At each pair $j,-j$ for which both factors are nonzero, their ratio must be a $p$-th power. Consequently $(t+z_j)^m=(t+z_{-j})^m$. A zero factor leaves that pair unrestricted. At $t\ne-1$ with $t^7\ne-1$, the extra test is $((t^7+1)/(t+1)^7)^m=1$ because $Q/D^6$ is a $p$-th power. No condition from this rational unit is imposed at its zeros or poles.

For each table row these tests leave at most $t=0,-1,\infty$. To enumerate the first pair, write $(t+z)/(t+z^{-1})=h$ with $h^m=1$. For $h\ne1$ this gives $t=(z-hz^{-1})/(h-1)$; add both possible zero factors and infinity. The independent checker uses $b/(a+b)$ and starts with a different conjugate pair. Here $m\le448$, even though the auxiliary primes reach 8,044,079.

At $t=-1$, $Q(a,b)=7b^6\bmod q$ is nonzero. The Frey elliptic curve is therefore good at $q$, and its reduction is isomorphic to $E_{-1,1}$ by weighted scaling. Since $7\nmid C$, Lemmata 4.5 and 4.8 of Dahmen–Siksek force its trace to agree modulo $p$ with that of $E_{1,0}$. The two models are $Y^2=X^3-4X^2-11X+43$ and $Y^2=X^3-X^2-2X+1$. The table supplies both traces at every $q$ and they disagree modulo $p$. Thus $q\mid ab$. For example at $p=11$ the row $q=617$ gives traces 6 and 30 in the order reference, specialization. [Dahmen–Siksek, §4.2](https://arxiv.org/pdf/1309.4030#page=18)

On either surviving axis the six values of $a+b\zeta$ are $p$-th powers in $\mathbb F_q^\times$. Indeed $D$ is a $p$-th power unit modulo $q$, and the six values are either $D$ or $Dz_j$. Each $z_j$ has order seven. The two character vectors of $(1+z_j)_j$ and $(1+z_j^2)_j$ are independent in $(\mathbb F_q^\times/\mathbb F_q^{\times p})^6$ for each row. The unit factorization now gives $r=s=0\bmod p$, proving the assertion. In particular the four unramified hyperelliptic curves of Dahmen–Siksek §4.3 apply across this entire interval.

## A local consequence including all primes that might divide the output

Assume $p\nmid ab$, put $t=a/b\in\mathbb Z_p$, and first suppose $p\nmid D$. Then $L_0=(t+\zeta)/(t+1)$ is an integral $p$-th power locally at all primes above $p$, by the preceding conclusion and $D=u^N$. This remains true if its numerator is a nonunit. With $\sigma(\zeta)=\zeta^p$, the unramified Frobenius test gives $\sigma(L_0)=L_0^p\bmod p^2$. In the ring with $Z^7=1$ this gives coefficientwise

$$ (t+1)(t+Z)^p-(t+Z^p)(t+1)^p=0\pmod{p^2}. $$

Indeed the left side vanishes modulo $\Phi_7$ and at $Z=1$, and 7 is invertible modulo $p^2$. For $x=t\bmod p$, the five coefficients $[Z^j](x+Z)^p$, $j\not\equiv0,p\bmod 7$, must all vanish modulo $p^2$. None of the 21,166,658 classes $1\le x\le p-2$ satisfies this necessary condition. This calculation includes the nontrivial seventh roots of $-1$.

If $p\mid D$, then $p^2\mid D$ and $t=-1\bmod p^2$. The integral unit $(a+b\zeta)^6/Q$ is a $p$-th power. Reducing gives $E=(\zeta-1)^6/7\bmod p^2$. For each of the 2,258 primes, $E^p\ne\sigma(E)\bmod p^2$, also checked by its $(p^f-1)$-st power with $f=\operatorname{ord}_7(p)$. This excludes the last slope. Hence $p\mid ab$ and automatically $p\nmid C$. If $N=p^e M$, the identity $u^{6N}-v^N=7ab(a^2+ab+b^2)^2$ and elementary odd-prime lifting give $v_p(ab)=e+v_p(u^{6M}-v^M)\ge e+1$, as in the [relative computation](../relative/README.md).

## The full prime-power exponent

The factors above also have ideals which are $p^e$-th powers for $e=v_p(N)$. Write $a+b\zeta=U^rV^s\gamma^{p^e}$, absorbing torsion as before. Modulo $p^{e+1}$, the left side is $D$ or $\zeta D$ since $p^{e+1}\mid ab$ and the bases are coprime. These are $p^e$-th powers. For $f=\operatorname{ord}_7(p)$, the two columns $(U^{p^f-1}-1)/p$, $(V^{p^f-1}-1)/p$ in $\mathcal O_L/p$ are independent for 2,255 primes. The three exceptions are 61, 5419 and 12703. In the table `units.txt`, the columns following $p$ give the two row indices and nonzero determinant of a minor for each of two methods, or a zero determinant when all minors vanish.

For independence, if $p^e$ does not divide both $r,s$, let $k=\min(v_p(r),v_p(s))<e$, treating $v_p(0)=+\infty$. On raising $U^rV^s$ to $p^f-1$, expansion modulo $p^{k+2}$ gives one plus $p^{k+1}$ times a nonzero linear combination of these columns modulo $p$. On the other hand $U^rV^s$ is a $p^e$-th power unit modulo $p^{e+1}$, so this expression must equal one modulo $p^{e+1}$. The contradiction proves $p^e\mid r,s$. Thus $a+b\zeta$ itself is a $p^e$-th power in $\mathcal O_L$ for all the indicated primes. Only the first power of the exponent is asserted at the three exceptions.

## Reproduction

`auxiliary.txt` consists of $(p,q,a_q(E_{1,0}),a_q(E_{-1,1}))$. PARI/GP is optional and is used only by the search for the auxiliary primes. The second verifier uses ordinary elliptic point addition and Hasse's bound. It intersects the allowed orders with multiples of point orders and falls back to direct point counting if necessary. It verifies the roots-of-unity enumeration and character rank separately. Run with Python 3.9+ and assertions enabled.

```sh
python3 check_aux.py auxiliary.txt 20000
c++ -O3 -std=c++17 pure.cpp -o pure
./pure 20000 > my-pure.txt
cmp my-pure.txt pure.txt
python3 units.py 20000 > my-units.txt
cmp my-units.txt units.txt
python3 check_local.py
# Optional regeneration using PARI/GP
python3 auxiliary.py 20000 gp > my-auxiliary.txt
cmp my-auxiliary.txt auxiliary.txt
```

`check_local.py` independently verifies the 4,520 singular-output slopes, using Teichmüller lifts in the split case. For the complementary slopes the independent computations in `../relative` apply directly. `units.py` compares all six coordinates of its two unit maps up to the requisite automorphism. All these results are necessary conditions and leave the global Beal equation unresolved.
