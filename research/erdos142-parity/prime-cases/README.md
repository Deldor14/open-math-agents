# Certified prime cases of a mixed van der Waerden conjecture

Maran, Reddy, Sharma and Tripathi conjectured in 2018 that w₂(p;p+2)=p(p−1)+3 for every prime p>3 (Conjecture 4.2, DOI 10.1216/RMJ-2018-48-3-885). In this notation w₂(p;p+2) is the least N for which p+1 points cannot meet every p-term arithmetic progression of positive stride in [1,N]. These finite computations concern the stated primes. They leave both the conjecture for all primes and the asymptotic equivalent in Erdős #142 open.

| p | N | Minimum hitting set size | r_p(N) |
|---:|---:|---:|---:|
| 11 | 113 | 13 | 100 |
| 13 | 159 | 15 | 144 |
| 17 | 275 | 19 | 256 |
| 19 | 345 | 21 | 324 |
| 23 | 509 | 25 | 484 |
| 29 | 815 | 31 | 784 |
| 31 | 933 | 33 | 900 |
| 37 | 1335 | 39 | 1296 |

For each listed p, the multiples of p up to p(p−1), together with 1 and 2, meet every progression on [1,N−1]. Adding 3 suffices on [1,N]. A step less than p traverses all residues modulo p. At step p the progression must start among the first two or three points, respectively. Larger steps cannot fit. Hence an UNSAT certificate for at most p+1 holes on [1,N] gives the exact maximum (p−1)² as well as the mixed van der Waerden number. The verifier independently enumerates both positive constructions.

## The formulas and the check

One primary variable per integer records whether it is a hole. Each progression contributes a positive clause. For a row consisting of one residue class modulo a stride, every contiguous block of k positions needs a hole, hence a prefix of length i contains at least floor(i/k) holes. The sum of these lower bounds on the other, disjoint rows gives a cap on the row. Applying the same argument to its suffix gives an upper bound on every prefix. Unary counters express the exact prefix counts inside these bounds. The four clauses at each threshold encode the update after adding a point. Constraints on contiguous blocks use the same disjoint-progressions argument. Every actual hitting set within budget therefore extends to a satisfying assignment. The full stride-one row enforces the total cardinality bound.

The original traces through p=31 were emitted by CaDiCaL 1.9.5 (python-sat 1.9.dev25). The p=37 trace was produced by CaDiCaL 2.1.2 on the same encoding. Independent verification used drat-trim; the p=37 checker was built from commit 2e3b2dc0ecf938addbd779d42877b6ed69d9a985. The public replay uses Python 3.9+ and drat-trim, with no SAT solver dependency. cases.json identifies the original CNFs, proofs and public compressed certificates with SHA-256. The logs directory records each original verdict. The compact proofs can be checked directly against a fresh copy of each original CNF.

    python verify.py --drat-trim /path/to/drat-trim
    python verify.py 29 31 37 --drat-trim /path/to/drat-trim
    python verify.py --cnf-only

For the archive containing the original uncompressed proof traces, run from this directory with the raw directory as an argument:

    python verify.py --raw ../raw --drat-trim /path/to/drat-trim

[Article](https://web.iitd.ac.in/~atripath/publications/mixed_van_der_Waerden.pdf) · [drat-trim](https://github.com/marijnheule/drat-trim)
