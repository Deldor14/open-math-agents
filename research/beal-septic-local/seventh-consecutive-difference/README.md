# A billion lower bound on the middle base in mixed septic Beal signatures

**Written proof and finite certificates for review.** There are no positive integers \(A,b,C,e\) with \(\gcd(A,b)=1,\ e\ge2,\ 1\le b\le10^9\), and
\[
                            A^7+b^e=C^7 .
\]
The output base \(C\), the other summand base \(A\), their distance, and the original exponent have no imposed upper bound. Consequently the same exclusion holds for \(A^i+B^j=C^r\) with \(7\mid i,r,\ j\ge2\), positive coprime summand bases, whenever \(B\) is **any positive power** of an integer at most one billion. Apply the displayed theorem to \(A^{i/7}\), \(C^{r/7}\), and the combined exponent of that integer. For example this covers \(B=23^k\) for every \(k\ge1\).

## Reduction to rational powers of a difference polynomial

Set \(D=C-A>0,\ Q=(C^7-A^7)/D\). The small prime factors \(2,3,5,7\) of \(e\) are excluded by the primitive signed results of Darmon–Merel, Dahmen–Siksek, and Fermat's last theorem. Theorem 1.4(1) of BCDF gives \(7\nmid D\) and \(2\mid AC\). Since \(\gcd(A,C)=1,\ \gcd(D,Q)=1\), we have \(D=d^e,\ Q=v^e,\ b=dv\), with \(d,v\) coprime odd positive integers. Every prime dividing \(Q\) is \(1\bmod14\), since \(C/A\) has exact order seven modulo it. In particular \(v\equiv1\bmod14\). Also \(Q\equiv1\bmod3\): if \(3\mid D\), then \(Q\equiv7A^6\equiv1\); otherwise use \(Q=D^6f(A/D)\), where \(f(X)=(X+1)^7-X^7\) takes only the value 1 over \(\mathbb F_3\). Thus \(v\equiv1\bmod42\). [BCDF, Theorem 1.4](https://arxiv.org/html/2308.07062v2#S1) · [Darmon–Merel](https://www.math.mcgill.ca/darmon/pub/Articles/Research/18.Merel/paper.pdf) · [Dahmen–Siksek](https://arxiv.org/abs/1309.4030)

Expanding the difference gives \(Q>D^6\). Hence \(v>d^6,\ d^7<dv\le10^9\), so \(d\) belongs to \(1,3,5,9,11,13,15,17,19\). At every prime \(q\nmid d\) there is a necessary residue condition
\[
                (v/d^6)^e \ \in\ f(\mathbb F_q).
\]
This follows from the exact identity \(f(A/D)=(v/d^6)^e\), so it also holds when \(q\mid v\).

## Two finite reductions

First set \(W=5040\). The allowed \(e\) are units modulo \(W\). For each prime \(q\ge5\) with \(q-1\mid W,\ q\nmid d\), the residue test depends only on \(e\bmod W\), even for zero base since \(e>0\). The [first program](sieve.cpp) scans every \(v\equiv1\bmod42,\ d^6<v\le10^9/d,\ \gcd(d,v)=1\). It intersects masks of the allowed exponent residues. The [independent program](independent.cpp) works in the opposite direction: it fixes an exponent class, inverts it modulo \(q-1\), and enumerates possible numerators by the Chinese remainder theorem. It calculates the image using the identity \(f(a)=1+7u(u+1)^2,\ u=a(a+1)\). The resulting sorted files agree byte for byte. There are [128 triples](classes.txt) and 97 different \((d,v)\). Every one satisfies \(v/(v-d^6)<9\).

We next bound the actual exponent **only after** this first reduction. For \(e\ge800000\) use equation (2) of the preceding full-order note at \(M=D\). Since \(v^e<7C^6\) and \(D=d^e\), it gives
\[
 e\log(v/d^6)<\big[354(3\log e+6.1)^2+2\big]\log v .
\]
The published estimate applies to arbitrary \(d\); its proof uses the exact cyclotomic height \(\log v/6\) and the two-logarithm bound of Laurent, Mignotte and Nesterenko. For each remaining row, \(\log(v/d^6)\ge(v-d^6)/v>1/9\) and \(\log v<21\). At \(e=300000000\), the right side after rearranging is bounded by \(189[354(3\cdot20+6.1)^2+2]<e\). Dividing by \(e\) makes this upper-bound function decreasing there and above, as one sees by differentiation. Hence every row has \(e<300000000\), including the cases below 800000. [Full-order note, equation (2) and exact constants](https://github.com/Deldor14/open-math-agents/tree/1033a3378ac62f1df9dd3dae7f4a839325afb7b0/research/beal-septic-local/seventh-full-order) · [Voutier, p. 255](https://www.numdam.org/item/JTNB_1996__8_2_251_0.pdf#page=5)

There are now 7,618,992 entries \((d,v,e)\), counting each exponent in its own row and omitting \(e=1\). For each row the [cover](cover.txt) lists additional primes, all at most 197, whose residue tests exclude every one of these entries. The [producer](cover.py) forms and intersects repeating bit patterns on the arithmetic progression. A [separate direct verifier](check-cover.py) enumerates those exponents, uses the integral polynomial \(1+7u(u+1)^2\), checks primality and valid denominators, and leaves no survivor.

## Reproduction

Use C++17 and Python 3.9 or later with assertions enabled. Run these commands from this directory.

    c++ -O2 -std=c++17 sieve.cpp -o sieve
    ./sieve > first.txt
    cmp first.txt classes.txt
    c++ -O2 -std=c++17 independent.cpp -o independent
    ./independent > second.txt
    cmp second.txt classes.txt
    python3 cover.py > new-cover.txt
    cmp new-cover.txt cover.txt
    python3 check-cover.py

The arithmetic exclusions have two independent checks at each finite stage. The uniform theoretical reduction is a written argument; the discrete inequalities formalized in the companion paper have their own Lean file. This suffices for the stated range of the middle base. The general Beal conjecture remains open.
