# Exact midpoint defects at one of two adjacent scales

Write $R(n)$ for the largest size of a subset of $[n]=\{0,\dots,n-1\}$ with no nonconstant three-term arithmetic progression. For a free set $A$ and $t\ge1$, let $T(A,t)$ be the minimum size of a set meeting every triple of three distinct points of $A$ with $|x+z-2y|\in\{t,2t\}$. Reordering the three points is allowed.

For every positive integer $N$, at least one length $n\in\{N,2N\}$ has the following property **simultaneously for all** free $A\subseteq[n]$ and all integers $1\le t\le n/26244$:
$$
 R(n)-|A|+T(A,t)> R(n)/50. \tag{1}
$$
The entire finite statement (1) is kernel-checked for mathlib's finite Roth number. In particular, if $|A|\ge0.99R(n)$, every joint cover has more than $R(n)/100$ points. Some one of the two defects then has more than $R(n)/600$ mutually disjoint witnesses. Indeed the union of a maximal disjoint family covers all the triples and at least half of the family has the same defect. The earlier good-length theorem used a growing window of dyadic lengths. Here two neighboring lengths suffice, and the steps at the two lengths may have unrelated parities. [Finite theorem in Lean](RothAdjacent.lean) · [Earlier dyadic-window theorem](RothInducedTriples.md)

A second, written proof improves $1/50$ in (1) to **$1/10$** at the same range of steps. It also gives a limiting coefficient $1-2/\sqrt5$ for sublinear steps. Its 42 finite phase choices are independently kernel-checked. The assembly argument for this stronger coefficient is given below.

## Five copies distributed over four phases

Delete a joint cover and call the remaining set $B$. With $P=\{x:x,x+t\in B\}$, put $p=|P|$. A previous result gives
$$
 4|B|\le3R(n+t)+2p,\qquad 4p\le R(2n+2t).
$$
Also if $x,y,z\in P$ and $x+z-2y$ is a multiple of $t$ of magnitude less than $5t$, then $x=y=z$. This includes repeated inputs. [Pair construction and root lemma](RothInducedTriples.md)

For each phase $c=0,1,2,3$ place above root $x$ all integers $Y$ satisfying
$$
 Y\equiv x\pmod t,\qquad ct\le 4Y-2x<(c+5)t.
$$
These lie in $[\lceil n/2\rceil+2t]$. In one phase a progression of outputs has input defect divisible by $t$ of magnitude less than $5t$, by taking second differences in the band. Its roots coincide and its outputs lie in the same fiber, which contains at most two points. Two coinciding outputs likewise have coinciding roots. Each root supplies five tagged sites over the four phases. Indeed its admissible errors form one residue class modulo $4t$; each of the four bands contains a full period and precisely one contains an additional representative in its last $t$ sites. Consequently
$$
 5p\le4R(\lceil n/2\rceil+2t).
$$
[Lean proof, including the projection, injectivity and count](RothHalfScale.lean)

For independent choices of free sets and steps $t,s$ at $N,2N$, let $d_1,d_2$ be their size deficits plus their joint cover sizes. Subadditivity and the three displayed inequalities imply
$$
 2R(N)\le40d_1+20d_2+35R(2t)+23R(2s). \tag{2}
$$
At length $n$, the first two inequalities give $2R(n)\le R(2n)+8d+7R(2t)$. The half-scale estimate gives $5R(n)\le8R(\lceil n/2\rceil)+20d+23R(2t)$. Substitution at the two lengths gives (2).

The ternary digits $0,1$ give $R(3^8)\ge256$, and the digit inequality gives $R(2t)R(3^8)\le R(4t\,3^8)$. Thus $26244t\le n$ implies $256R(2t)\le R(n)$. If (1) failed at both lengths, (2) and $R(2N)\le2R(N)$ would give $2\le80/50+81/256$, a contradiction. The same proof works with the size of the union of any two individual covers. [Full kernel checks](RothAdjacent.lean)

## A larger coefficient from the seven component shapes

Let $W(n,t)$ be the largest size of such a $B$, avoiding both exact defects as well as ordinary progressions. We obtain
$$
 2W(n,t)\le R(2n+3t),\qquad
 5W(2n,s)\le 8R(n+s). \tag{3}
$$
Here is the finite selection and its assembly. For slope $\lambda$, above each $x$ consider integer $Y\equiv x\pmod t$ in the half-open band from $\lambda x+c$ to $\lambda x+c+3\lambda t/2$, for a common real $c\in[0,t)$. An output progression has input defect a multiple of $t$ of magnitude strictly less than $3t$. Weak avoidance forces at least two inputs equal. The distinct inputs in such a progression differ by $t/2,t$ or $2t$. A collision of outputs also has inputs equal or separated by one of these distances. Thus free choices from different connected components of the graph with these distances can be combined without collisions or progressions. Each component based at its smallest point $a$ has form $a+(t/2)C$ for one of the seven shapes listed below, by the earlier classification. [Classification and gluing criterion](RothDyadicClusters.md)

Write $\lambda=p/q$ in lowest terms. The candidates in relative coordinates $u=2(Y-a)/t$ from $j\in C$ have $u\equiv j\pmod2$ and
$$
 pj+h\le qu<pj+h+3p,\qquad
 h=\left\lceil 2q((\lambda-1)a+c)/t\right\rceil.
$$
Adding $2q$ to $h$ translates all candidates by two relative units. As $c$ ranges uniformly over $[0,t)$, each class mod $2q$ has equal probability, even though different components need not have the same phase. Every candidate is an actual integer site since it differs from its generating input by an integer multiple of $t$. For each shape the following are the average numbers of selected local sites divided by $|C|$.

| Relative coordinates $C$ | Slope $1/2$ | Slope $2$ |
|---|---:|---:|
| $0$ | $3/4$ | $2$ |
| $0,1$ | $3/4$ | $2$ |
| $0,2$ | $5/8$ | $2$ |
| $0,4$ | $3/4$ | $2$ |
| $0,1,5$ | $3/4$ | $2$ |
| $0,4,5$ | $3/4$ | $2$ |
| $0,4,5,9$ | $3/4$ | $2$ |

At one common phase the sum is at least its mean. The integer sites fit inside a translate of an interval of $\lceil\lambda(n-1)+3\lambda t/2\rceil$ sites. At slope two this gives the first inequality in (3), and applying slope one half at length $2n$ gives the second. [Lean certificates for all 42 selections](RothAdjacentWindows.lean) · [Independent exhaustive enumeration](check_roth_adjacent.py)

To obtain the stated finite coefficient, put $M=R(N)$ and $H=R(2N)$. When $H/M\le43/24$, the first part of (3) gives $W(N,t)/M\le43/48+1/256<9/10$. Here $R(3t)\le2R(2t)\le2M/256$. When $H/M>43/24$, the second part gives $W(2N,s)/H\le(8/5)(24/43+1/256)<9/10$. These alternatives hold for every admissible step at the selected length. Removing a joint cover gives $|A|-T(A,t)\le W(n,t)$, as required.

For any prescribed $H_0(n)=o(n)$, the same digit inequality makes boundary costs $o(R(n))$ uniformly for $t\le H_0(n)$. The minimum of the two normalized bounds from (3) is at most
$$
 \min\{x/2,8/(5x)\}+o(1)\le 2/\sqrt5+o(1),\qquad x=R(2N)/R(N).
$$
Thus at one of $N,2N$ the combined size deficit and joint cover cost is at least $(1-2/\sqrt5-o(1))R(n)$ for all such steps and sets. The ordinary Roth number at a single arbitrary length, and the explicit asymptotic asked for in [Erdős problem 142](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/142.lean), remain undetermined.
