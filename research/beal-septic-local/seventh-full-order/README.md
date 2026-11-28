# Two primitive divisors of exact order N in the mixed septic equation

**Written proof for review.** Suppose \(A^7+B^N=C^7\), with \(A,B,C\) positive integers, \(\gcd(A,B)=1\), and \(N\ge2\). Put \(D=C-A\) and \(H=\max(A,D)\). For each of \(C,H\) there is a prime divisor \(r\ne7\) such that a norm-one cyclotomic ratio has **exact order \(N\)** in a residue field above \(r\). In particular \(N\mid m_r\), where, with \(f=\operatorname{ord}_7(r)\),
\[
 m_r=\begin{cases}r^f-1&f\text{ odd},\\r^{f/2}+1&f\text{ even}.\end{cases}
\]
The two rational primes are distinct. This gives a single witness for the entire exponent on each of the two bases, including when \(N\) has several distinct prime factors. If every prime factor of \(N\) is \(2\bmod3\), each witness is at least \(2N-1\): the factors \(r^2\pm r+1\) in \(m_r\) have no prime divisor of this type above 3, so \(N\mid r-1\) for odd \(f\), and \(N\mid r+1\) for even \(f\). Also \(r=2\) cannot witness since \(m_2=7\). The earlier lcm condition allowed different primes for the different factors of \(N\). [Earlier result](https://github.com/Deldor14/open-math-agents/tree/71e7e0772fd9f45c80adee172f95b43d0398f71e/research/beal-septic-local/seventh-output-support)

If \(N\ge2{,}000{,}000\), **all three** of \(A,C,D\) have such witnesses, giving three distinct rational primes, and both \(A\) and \(D\) exceed \(\sqrt C\). In the consecutive case \((A+1)^7-A^7=B^N\), we obtain the absolute bound **\(N<800{,}000\)**, independent of \(A\). These claims use no class-number computation in a field of growing degree. The fixed field throughout the factorization is \(K=\mathbb Q(\zeta_7)\).

## The integral numerator and denominator

The cases \(2,3,5,7\mid N\), meaning that any one of these primes divides \(N\), are excluded by the signed primitive results of Darmon–Merel, Dahmen–Siksek and Fermat's last theorem. Hence all prime factors of \(N\) are at least 11. BCDF Theorem 1.4(1) gives \(7\nmid D,\ 2\mid AC\). Set \(Q=(C^7-A^7)/D\); \(\gcd(D,Q)=1\) and \(Q=v^N\) with \(v\ge29\). Indeed \(Q>1\), it is odd, and \(C/A\) has order 7 modulo every prime divisor of \(Q\), making each such prime \(1\bmod14\). Also \(Q<7C^6\). [BCDF](https://arxiv.org/html/2308.07062v2#S1) · [Darmon–Merel](https://www.math.mcgill.ca/darmon/pub/Articles/Research/18.Merel/paper.pdf) · [Dahmen–Siksek](https://arxiv.org/abs/1309.4030)

Write \(z=\zeta_7,\ \alpha=C-Az\). The ideals of \(\alpha\) and its five conjugates are pairwise coprime: a common prime would lie over 7 and divide \(D\). Since their product is \(Q\) and the class number of \(K\) is one, \(\alpha=\epsilon\gamma^N\) with \(\gamma\) integral and \(\epsilon\) a unit. Here \(\lvert\mathrm{Nm}(\gamma)\rvert=v\), the ideals of \(\gamma,\bar\gamma\) are coprime, and \(\epsilon/\bar\epsilon\in\mu_{14}\) by Kronecker's theorem. [Field and unit data](https://arxiv.org/pdf/1309.4030#page=15)

For \(M=C,A,D\) respectively set \(\kappa=z^2,1,-z\). The numerator \(\alpha-\kappa\bar\alpha\) is \(C(1-z^2),-A(z-z^{-1}),D(1+z)\), respectively. Since \(\gcd(N,14)=1\), we can choose coprime integral \(u,w\) with \(w=\bar\gamma,\ u\in\mu_{14}\gamma\) so that
\[
 \theta=u/w,\qquad \theta^N=\alpha/(\kappa\bar\alpha).
\]
For each \(M\) this choice of \(\theta\) is the one used in the exact-order assertion. Every conjugate has absolute value 1. Its absolute logarithmic height is \(h(\theta)=\log v/6>0\): the denominator ideal has norm \(v\), there is no cancellation, and there is no archimedean contribution. At every place over a prime \(r\mid M\), both \(u,w\) are units (for \(D\) use \(\gcd(D,Q)=1\)).

## Removing the proper orders

Let \(F_N(X)=(X^N-1)/\Phi_N(X)\), put \(t=\omega(N)\), \(j=2^{t-1}\) and \(K_N=2^j(N+1)^{j-1}\). The sum of the absolute coefficients of \(F_N\) is at most \(K_N\). Indeed its formal series at zero, up to a sign, is the product of \((1-X^e)^{-\mu(N/e)}\) over \(e\mid N,\ e<N\). It has \(j\) numerator factors and \(j-1\) denominator factors. Each reciprocal factor truncated at degree \(N\) has coefficient sum at most \(N+1\). The part of the product of degree at most \(N\) gives the entire polynomial. In particular \(K_N=2\) for a prime power.

Suppose no prime ideal above any \(r\mid M\) gives \(\theta\) exact order \(N\). At \(r^h\parallel M\), we have \(\theta^N=1\bmod r^h\). Its residual order \(a\) properly divides \(N\). If \(r\nmid N\), the factors of \(X^N-1\) have disjoint roots in the residue field, so \(\Phi_N(\theta)\) is a unit. If \(r\mid N\), write \(N=mr^b,\ r\nmid m\). The reduction of \(\Phi_N(X)\) is \(\Phi_m(X)^{\varphi(r^b)}\), so only \(a=m\) requires attention. In that case use
\[
 \Phi_N(X)=\Phi_m(X^{r^b})/\Phi_m(X^{r^{b-1}}).
\]
At \(\theta^{r^i}\) the other factors of \(X^m-1\) are units. The difference of the two valuations therefore equals 1 by binomial lifting in the unramified field at \(r\ge11\). No denominator in this valuation comparison vanishes, since \(\theta\) has positive height. For \(r=7\) the first, separable case already applies. Thus \(M/\gcd(M,N)\) divides the homogeneous polynomial value \(w^{N-\varphi(N)}F_N(u/w)\) in \(\mathcal O_K\). This value is a nonzero algebraic integer. Its absolute norm is at most \(K_N^6 v^{N-\varphi(N)}\), by applying the coefficient bound to each conjugate of \(\theta\) and using the exact norm of \(w\). In particular,
\[
 M \le N K_N\,v^{(N-\varphi(N))/6}. \tag{1}
\]

For \(2M\ge C\), use \(v^N<7C^6\) in (1) to obtain \(29^{\varphi(N)/6}\le v^{\varphi(N)/6}<3N K_N\). This is impossible. Here are details of the uniform numerical inequality.

* For a prime power \(N=q^a\), one has \(N^2\le 2^{\varphi(N)}\). This follows from \(q\le 2^{(q-1)/2}\) for odd \(q\ge11\) and \(a\le q^{a-1}\). If \(\varphi(N)\ge18\), then \(6^6<2^{\varphi(N)}\) and \((6N)^6<16^{\varphi(N)}\). The three remaining \(N=11,13,17\) satisfy \((6N)^6<29^{\varphi(N)}\) directly.
* For \(t\ge2\), \(3NK_N<N^{2^t+1}\), since \(2(N+1)\le N^2\). For each prime-power factor \(q^a\parallel N\) use \(2\log_2(q^a)\le\varphi(q^a)\). The other \(t-1\) totients are each at least 10. Summing gives \(2\log_2N\le t\varphi(N)/10^{t-1}\). Since \(t(2^t+1)\le10^{t-1}\) for \(t\ge2\), we have \(N^{6(2^t+1)}\le8^{\varphi(N)}<29^{\varphi(N)}\).

This proves exact order for \(M=C,H\). A prime above 7 cannot work, as its residue field has order 7. For an even residue degree, complex conjugation acts by the \(r^{f/2}\)-power Frobenius and \(\bar\theta=\theta^{-1}\); hence \(N\mid m_r\). For odd \(f\) use the full residue group. Finally \(\gcd(C,H)=1\).

## The smaller base and differences of consecutive powers

Fix the complex embedding \(z=\exp(6\pi i/7)\). Its negative real part gives \(|\bar\alpha|\ge C\), and each of \(1-z^2,z-z^{-1},1+z\) has absolute value at most 1. For the corresponding \(\theta\), therefore,
\[
                 |\theta^N-1|\le M/C .
\]
We detail the constants in the two-logarithm lower bound so the consecutive-exponent cutoff is reproducible. For \(N\ge800000\), change \(\theta\) by a sign and, if necessary, complex conjugation to get \(\gamma_0\) with argument in \([0,\pi/2]\). Choose a nonnegative integer \(b\) of the parity needed for \((-1)^b\) to have the sign removed from \(\theta^N\), nearest to \(N\arg(\gamma_0)/\pi\) within that parity. Then \(b\le N/2+1\), and \(\Lambda=b\pi i-N\log\gamma_0\) has absolute value at most \(\pi\). It is nonzero by positive height. The chord bound gives \(|\theta^N-1|\ge (2/\pi)|\Lambda|\).

Use the Laurent–Mignotte–Nesterenko bound as stated in Voutier, p. 255, equation (1), with degree \(d\le6\), \(b_1=b,\ b_2=N\). For \(b>0\) it gives \(\log|\Lambda|\ge-9aH_0^2\), where
\[
 a=\max(20,12.85|\log\gamma_0|+d h(\gamma_0)/2),\quad
 H_0=\max(17,(d/2)\log(b/(2a)+N/(25.7\pi))+2.3d+3.25).
\]
Since \(h(\gamma_0)=\log v/6\) and \(v\ge29\), \(a<6.55\log v\). The argument of the logarithm in \(H_0\) is at most \((N+1)/40<N/39\); hence \(H_0<3\log N+6.1\). For \(b=0\) the same lower bound with these upper estimates follows from \(|\Lambda|\ge|\gamma_0-1|\ge1/(32v)\), since the denominator ideal of \(\gamma_0-1\) has norm \(v\) and its other five conjugates have absolute value at most 2. Altogether,
\[
 \log(C/M)\le\log(\pi/2)+9(6.55)\log v\,(3\log N+6.1)^2. \tag{2}
\]
[Voutier, equation (1)](https://www.numdam.org/item/JTNB_1996__8_2_251_0.pdf#page=5) · [Laurent–Mignotte–Nesterenko, Théorème 3](https://doi.org/10.1006/jnth.1995.1141)

Write \(U(x)=354(3\log x+6.1)^2\). If \(M=1\), equations (2) and \(v^N<7C^6\) imply \(N<U(N)+2\). But \(U(800000)+2<800000\), and \((U(x)+2)/x\) is decreasing on that half-line. This proves the claimed restriction when \(D=1\).

If \(N\ge2000000\) and \(M\) lacked an exact-order place, (1) and (2) would give
\[
 \varphi(N)< U(N)+2+2N^{0.3}\log N .
\]
Here \(NK_N\le N^{2^t}\), \(2^t\le N^{0.3}\) and \(6/\log v<2\). On the other hand \(\varphi(N)\ge(10/11)^tN\ge N^{0.96}\). The displayed upper bound is strictly less than \(N^{0.96}\) for \(N\ge2000000\). At the left endpoint the upper bound is below 1,000,000 and \(N^{0.96}\) is above it. Dividing each upper-bound term by \(x^{0.96}\) gives a decreasing function there, as is seen by logarithmic differentiation. Therefore the smallest of \(A,D\) also has an exact-order place. Pairwise coprimality makes the three rational witnesses distinct. If \(M\le\sqrt C\), (2) instead gives \(N<2U(N)+3\); the same decreasing-ratio check, with \(2U(2000000)+3<2000000\), excludes this possibility.

## Reproduction and scope

The exact rational endpoint inequalities are in [check.py](check.py), using Taylor sums with a geometric upper bound for the tails. [FullOrder.lean](FullOrder.lean) checks the discrete growth bounds and the small totients. [polynomial.gp](polynomial.gp) checks the cofactor identity and bounds on a finite sample. The universal local valuation, norm and logarithm arguments are written above for review.

    python3 check.py
    gp -fq -s 80M polynomial.gp
    lean FullOrder.lean
