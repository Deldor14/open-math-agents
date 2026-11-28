# Prime support of the output base in mixed septic signatures

**Written proof for review.** Suppose \(A^7+B^N=C^7\), where \(A,B,C\) are positive integers, \(\gcd(A,B)=1\), and \(N\ge2\). Set \(D=C-A\) and \(H=\max(A,D)\). For a rational prime \(r\ne7\) let \(f=\operatorname{ord}_7(r)\) and define
\[
 m_r=\begin{cases}r^f-1&f\text{ odd},\\r^{f/2}+1&f\text{ even}.\end{cases}
 \qquad m_7=1,\qquad L(u)=\operatorname{lcm}_{r\mid u,\ r\ {\rm prime}}m_r,\quad L(1)=1.
\]
Then
\[
                 N\mid\gcd\big(L(C),L(H)\big).
\]
In particular, for every prime power \(p^k\parallel N\), **two distinct rational primes** \(r\mid C,\ s\mid H\) satisfy \(p^k\mid m_r,m_s\). The choice of \(r,s\) can depend on \(p\). If \(p=2\bmod3\), each is at least \(2p^k-1\). The criterion uses the signed cyclotomic factorization and the published small-exponent results. It is independent of the companion Jacobian descents and of the 100,000 cutoff. [Assigned mixed-exponent leaf](https://lefttosolve.com/p/BealConjecture.beal_conjecture.R3.H1) · [Previous signed-entry and large-prime argument](https://github.com/Deldor14/open-math-agents/tree/720d396e0fe93c1a854e673e64ba7e44daf2ad89/research/beal-septic-local/mixed-seventh)

## Proof

The signed primitive triple is \((C,-A,B)\). Any common prime of \(C,A\) divides \(B\), and \(D>0\). For \(p=2,3,5,7\) dividing \(N\) the corresponding signed primitive equation is excluded by Darmon–Merel, Dahmen–Siksek or Fermat's last theorem. We therefore take \(p^k\parallel N,\ p\ge11\). BCDF Theorem 1.4(1) gives \(2\mid AC,\ 7\nmid D\). With \(Q=(C^7-A^7)/D\), we have \(\gcd(D,Q)=1\) since a common prime must divide 7. Thus \(D=d^N\) and \(Q=v^N\), with \(d,v>0\); put \(V=v^{N/p}\). Every prime \(t\mid Q\) is \(1\bmod 14\). Indeed \(Q\) is odd, \(t\nmid ACD\), and \(C/A\) has exact order 7 in \(\mathbb F_t^\times\). Since \(Q>1\), this gives \(V\ge29\). Here \(D\) is odd and \(Q=\sum_{j=0}^6 C^{6-j}A^j<7C^6\). [BCDF, Theorem 1.4](https://arxiv.org/html/2308.07062v2#S1) · [Darmon–Merel](https://www.math.mcgill.ca/darmon/pub/Articles/Research/18.Merel/paper.pdf) · [Dahmen–Siksek, Theorem 2](https://arxiv.org/abs/1309.4030)

Let \(\zeta=\zeta_7\), \(K=\mathbb Q(\zeta)\), \(\alpha=C-A\zeta\), \(R=\alpha/\bar\alpha\). The seven factors \(C-A\zeta^i\) have pairwise coprime ideals: a common prime would force \(7\mid D\). The product is \(B^N\); as \(K\) has class number one, \(\alpha=\epsilon\gamma^{p^k}\) for a unit \(\epsilon\) and integral \(\gamma\). The quotient \(\epsilon/\bar\epsilon\) has all conjugates of absolute value 1 and is a root of unity of order dividing 14. Hence \(R\) has a \(p^k\)-th root in \(K\). All its conjugates have absolute value one. [Cyclotomic field data in Dahmen–Siksek, §4.1](https://arxiv.org/pdf/1309.4030#page=15)

For \(M=C,A,D\), respectively, take \(\kappa=\zeta^2,1,-\zeta\). In that order the numerators \(\alpha-\kappa\bar\alpha\) equal \(C(1-\zeta^2),-A(\zeta-\zeta^{-1}),D(1+\zeta)\). Each is nonzero. Choose \(\theta\in K\) with \(\theta^{p^k}=R/\kappa\), absorbing a root of \(\kappa\) in \(\mu_{14}\). Then \(\theta\bar\theta=1\). Put \(\eta=\theta^{p^{k-1}}\). The number \(V(\eta-1)\) is a nonzero algebraic integer: \((V\eta)^p=Q\alpha/(\kappa\bar\alpha)\) is integral because \(\bar\alpha\) is a factor of \(Q\).

Let \(r^h\parallel M\) and \(w\mid r\) in \(K\). Both \(V,\bar\alpha\) are units there. For \(M=A,C\) this follows from coprimality of \(A,C\), and for \(M=D\) it follows from \(\gcd(D,Q)=1\). Thus \(\theta^{p^k}=1\bmod r^h\mathcal O_{K,w}\). At \(r\ne7\) the residue degree is \(f\). For even \(f\), complex conjugation acts there by the \(r^{f/2}\)-power Frobenius, since \(r^{f/2}=-1\bmod7\). The residue of \(\theta\) lies in the norm-one subgroup of order \(r^{f/2}+1\). For odd \(f\) the whole residue group has order \(r^f-1\). At \(r=7\) the residue has order dividing 6, prime to \(p\). These assertions hold at every place over \(r\).

If \(p^k\nmid m_r\), the residue of \(\theta\), whose order divides \(p^k\), is killed by \(p^{k-1}\). Consequently \(\eta=1\) in the residue field. For \(r\ne p\) the geometric factor in \(\eta^p-1\) is a unit and \(\eta-1\in r^h\mathcal O_{K,w}\), including ramified 7. For \(r=p\), the extension is unramified, \(p\) is odd, and the binomial expansion gives \(v_w(\eta-1)\ge h-1\) when \(v_w(p)=1\). The relation \(\eta^p=R/\kappa\ne1\) makes all these valuations finite.

For any of the three \(M\) define \(M_*\) as the product of the full powers of rational primes \(r\mid M\) for which \(p^k\mid m_r\). The congruences show that \(M/(M_*\gcd(M,p))\) divides \(V(\eta-1)\) integrally in \(K\), since \(p^k\nmid m_p\). Every conjugate of that nonzero integer has absolute value at most \(2V\). Taking absolute norms yields the quantitative bound
\[
                       M/M_* \le 2V\gcd(M,p).
\]
In particular, if \(2M\ge C\) and \(M_*=1\), then \(C\le4pV\) and \(V^{p-6}<7(4p)^6\). For \(p\ge17\), \(29^{p-6}>7(4p)^6\). The inequality holds at 17 and propagates using \(2(p+1)\le3p\), since \(3^6<29\cdot2^6\).

For \(p=11\) the same bound forces \(V\le138\), and for \(p=13\) it forces \(V\le39\). Since every prime of \(V\) is \(1\bmod14\) and at least 29, \(V\) must be a single prime in these ranges. The candidates are \(29,43,71,113,127\) for 11 and \(29\) for 13. In either case \(D=d^N<C\le4pV\le6072<3^{11}\). As \(d\) is odd and \(N\ge11\), it follows that \(D=1\). Hence \((A+1)^7-A^7=V^p\). Modulo 83 the six respective right sides are \(69,79,35,59,41,12\); none occurs on the left. The [Lean file](Support.lean) proves the growth estimates and all six residue exclusions.

Thus \(M_*>1\) whenever \(2M\ge C\). Apply this to \(C\) and to \(H=\max(A,D)\) using \(A+D=C\). These two integers are coprime since \(\gcd(C,A)=\gcd(C,D)=1\). The two prime witnesses are distinct, and applying the result to every full prime-power factor of \(N\) proves the asserted lcm divisibility. When \(p=2\bmod3\), a factor \(r^2+r+1\) of \(r^3-1\), or \(r^2-r+1\) of \(r^3+1\), cannot be divisible by \(p\ge11\). Otherwise \(r\) has order 3 or 6 modulo \(p\), with the exceptional repeated roots possible only for \(p=3\). Hence \(p^k\mid r-1\) for odd \(f\) and \(p^k\mid r+1\) for even \(f\). The prime \(r\) cannot be 2, whose \(m_2=7\). Its odd parity gives \(r\ge2p^k-1\).

## Explicit consequences for restricted prime factors

Among the 9,592 rational primes up to 100,000, 203 have \(m_r\) with no prime divisor \(\ge11\), including \(r=7\) by convention. Neither \(C\) nor \(H\) can be supported entirely on those 203 primes. There is no bound on their exponents or the third base. Adding the companion signed exclusions gives a set of 1,952 primes on which neither can be supported. For example \(C\) must have a prime divisor at least 23 under this strengthened statement. The file [support.txt](support.txt) uses “local” for the first set and “descent” for its 1,749 additional members. Two independent programs factor the torus orders, one through their cyclotomic factors in Python and the other directly in PARI/GP. [Signed descent input for the second set](https://github.com/Deldor14/open-math-agents/tree/720d396e0fe93c1a854e673e64ba7e44daf2ad89/research/beal-septic-local/mixed-seventh)

If \(C\) and \(H\) are powers of distinct primes \(r,s\le100000\), the gcd obstruction alone excludes 41,717,266 of the 45,998,436 unordered pairs \(\{r,s\}\). Using the signed descents increases the excluded count to 45,420,415. These are counts of prime supports; the powers of \(r,s\) in either role are unrestricted. The program counts by both inclusion-exclusion on squarefree divisors and intersections of the prime incidence sets. The residual list is necessary only.

To reproduce from this directory:

    python3 support.py > computed.txt
    gp -fq independent.gp > second.txt
    cmp support.txt computed.txt
    cmp support.txt second.txt
    python3 pairs.py
    lean Support.lean

The size and finite residue lemmas were compiled with Lean 4.33.1 and Mathlib. The cyclotomic and norm argument is given above for mathematical review.
