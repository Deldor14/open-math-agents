# A gap bound for quintic sums and the case of consecutive bases

**Theorem.** For positive integers $x,y$ and an integer $n\ge 2$,

$$x^5+(x+1)^5=y^n$$

has no solutions.

The key estimate is a bound on a primitive solution with any prescribed difference of bases. It gives a short proof of the theorem when combined with Ákos Pintér's Theorem 2.8. We give a second verification using Laurent's two-logarithm bound and a small exact sieve, independent of the continued fractions and numerical certificates in Pintér's preprint. This is a research note submitted for review. The general Beal conjecture allows arbitrary bases and exponents.

## The gap estimate

Let $a,b$ be distinct positive coprime integers, $p\ge 7$ a prime, and $a^5+b^5=c^p$. Write $D=a+b$ and $d=|a-b|$. Theorem 5 of Billerey–Chen–Dieulefait–Freitas excludes $5\mid D$. Thus $D=u^p$ for a positive integer $u$, since the gcd of $D$ and $(a^5+b^5)/D$ divides 5. We prove

$$u<8pd.$$

The argument below needs only $5\nmid D$, the power equation and coprimality. [BCDF, Theorem 5](https://arxiv.org/pdf/1703.06530)

Take $K=\mathbb Q(\zeta)$, with $\zeta=e^{2\pi i/5}$, and $\varepsilon=1+\zeta+\zeta^{-1}=(1+\sqrt5)/2$. The five factors $a+b\zeta^i$ of $c^p$ are pairwise coprime as ideals. Indeed a common prime ideal would divide either $b$ and $a$, or a difference of distinct fifth roots, in which case it lies over 5 and divides $D$. The class number of $K$ is one by the Minkowski bound $(4!/4^4)(4/\pi)^2\sqrt{125}<2$. Its units are $\mu_{10}\langle\varepsilon\rangle$. To recall the latter fact, for a unit $v$ all conjugates of $v/\bar v$ have modulus one. By Kronecker it is a root of unity and reduces to 1 at $1-\zeta$, hence belongs to $\mu_5$. Removing its square root in $\mu_5$ from $v$ leaves a real unit. The real quadratic units are $\pm\varepsilon^m$. Because $(p,10)=1$, we obtain

$$a+b\zeta=\varepsilon^j\gamma^p,\qquad 0\le j<p,\quad \gamma\in\mathbb Z[\zeta].$$

Choose $e$ with $2ep\equiv-1\pmod 5$ and put $\omega=\zeta^e$, $X=\omega\gamma$, $Y=X-\bar X$, $Z=X^p-\bar X^p$. Since $\bar\omega^p=\omega^p\zeta$,

$$Z=\varepsilon^{-j}\omega^p(a-b)(1-\zeta).$$

In particular $Z\ne0$, the algebraic integer $Y$ divides $Z$, and $|N_{K/\mathbb Q}(Z)|=5d^4$. Subscripts 1 and 2 denote the complex embeddings $\zeta\mapsto\zeta$ and $\zeta\mapsto\zeta^2$. Since the remaining embeddings are their conjugates,

$$1\le |Y_1Y_2|\le\sqrt5\,d^2.$$

Choose $i$ such that $|Y_i|\le 5^{1/4}d<2d$. For either embedding, $D/4<|a+b\zeta^i|\le D$. For the lower bound, divide by $D$ to obtain a point on the segment between 1 and $\zeta^i$, whose distance from zero is at least $\cos(2\pi/5)>1/4$. Both conjugate values of $|\varepsilon|$ lie strictly between $1/2$ and 2. Thus

$$u/4<|X_i|<2u$$

for either $i$, using $p\ge 7$. At the other embedding $h$ we have $|Y_h|\le 2|X_h|<4u$. The lower norm bound therefore gives $|Y_i|>1/(4u)$.

Suppose $u\ge 8pd$. Set $z=\bar X_i/X_i$. Then $|z|=1$ and $(p-1)|1-z|<1$. The geometric identity implies $|z^k-1|\le k|z-1|$, so

$$\left|\sum_{k=0}^{p-1}z^k-p\right|\le \tfrac12 p(p-1)|z-1|\le p/2.$$

It follows that

$$2^p d>|Z_i|=|Y_i|\,|X_i|^{p-1}\left|\sum_{k=0}^{p-1}z^k\right|>\frac{p}{32}(u/4)^{p-2}.$$

The first inequality uses $j\le p-1$ and $|1-\zeta^i|<2$. But $u/4\ge 2pd$, and $p^{p-1}d^{p-3}>128$ for $p\ge7$, $d\ge1$. The last expression exceeds $2^p d$, a contradiction. This proves the gap estimate.

## A short deduction for consecutive bases

For $n\ge3$, Pintér's Theorem 2.8 implies that any positive solution has prime exponent $23\le n\le 181$, with $2x+1=u^n$ and $u>10^{1000}$. The gap estimate with $d=1$ gives $u<8n\le1448$. These inequalities are incompatible. The square case is already excluded by Poonen's Theorem 1.6. [Pintér, Theorem 2.8](https://arxiv.org/pdf/2611.29398) · [Poonen, Theorem 1.6](https://doi.org/10.4064/aa-86-3-193-205)

## Alternative verification using a coarse bound and finite arithmetic

For this verification take any prime $p\mid n$ and absorb the remaining exponent into $c$. Poonen excludes $p=2,3$, and Fermat's last theorem excludes $p=5$. For $p\ge7$, write $a=x$, $b=x+1$. The coprime factors $D$ and $(a^5+b^5)/D$ give coprime positive odd integers $u,v$ with

$$D=u^p,\qquad 16v^p=u^{4p}+10u^{2p}+5.$$

Here $u\ge3$. The identity follows by expanding the cofactor in $a+b$ and $a-b$. The gap estimate gives $u<8p$.

We recall the short logarithmic bound used in §4.2 of Pintér, giving details so the rest of that computation is unnecessary. Put $L=\log u$ and $\alpha=u^4/v$. We have $\alpha>1$ because $16u^{4p}-(u^{4p}+10u^{2p}+5)=5(u^{2p}-1)(3u^{2p}+1)>0$. It is a quotient of odd integers and is multiplicatively independent of 2. Its logarithmic height is $4L$. Set

$$\Lambda=4\log 2-p\log\alpha=\log(1+10u^{-2p}+5u^{-4p}).$$

Then $0<\Lambda<10u^{-2p}$ by the exponential series. Apply Laurent's Corollary 2 with $D_{\rm field}=1$, $m=10$, $C_2=25.2$, $\log A_1=4L$, $\log A_2=1$, coefficients $p,4$. All height and positivity conditions hold, and $b'=p+1/L$. This gives

$$p<50.4\max\{\log(p+1/\log 3)+0.38,10\}^2+\frac{\log 10}{2\log 3}.$$

At $p=5042$ the maximum is 10 and the last term is less than 2, so the right side is less than 5042. Its ratio to $p$ decreases for $p\ge5042$. Indeed on the logarithmic branch the derivative of $M^2/p$ has the sign of $2p/(p+1/\log3)-M<0$, and on the constant branch it decreases directly. Thus $p\le5041$. [Laurent, Corollary 2 and Table 1](https://doi.org/10.4064/aa133-4-3) · [Pintér, §4.2](https://arxiv.org/pdf/2611.29398)

For each such prime $p$, test all the odd integers $3\le u<8p$. At a witness prime $q\equiv1\pmod p$, set $t=u^p\bmod q$. A necessary condition is

$$t^4+10t^2+5\ \in\ 16\{v^p:v\in\mathbb F_q\}.$$

Zero is included throughout. The certificate eliminates all **6,312,256** pairs across **672** prime exponents. It contains 3,145 tests, with largest auxiliary prime 537,899. No upper bound on $x$ is assumed. This proves the same theorem without using the continued-fraction bounds, determinant optimizations or finite solution counts in Pintér.

Run `python3 verify_quintic_gap.py` with `quintic_gap_witnesses.txt` in the same directory. The verifier checks primality, exact exponent coverage, all base candidates and complete cyclic subgroups via primitive roots. The certificate was constructed independently using the exponent criterion for power residues. The Lean file `GapChecks.lean` verifies the geometric-sum bound and the centered polynomial identity in Lean 4.33.1. The cyclotomic descent and the application of Laurent's theorem are written mathematical proofs.
