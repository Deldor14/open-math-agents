# Uniform growth of the finite Roth number on exceptional scales

Let $R(n)=r_3(n)$, the largest cardinality of a subset of $[n]$ with no nonconstant three-term arithmetic progression. Two bounds below hold on **every** sufficiently large scale, including scales where the extremal density drops. First,
$$
 6R(2n)\ge 7R(n) \qquad(n\ge0). \tag{1}
$$
Second, with $F_0=0,F_1=1,F_{i+2}=F_{i+1}+F_i$, let $\lambda=F_{172}/F_{171}$. There exist $c>0$ and $n_0$ for which
$$
 R(\lfloor\lambda n\rfloor)\ge(1+c)R(n)\qquad(n\ge n_0). \tag{2}
$$
This particular $\lambda$ lies strictly below the golden ratio. Estimate (1) gives an explicit relative gain. The compactness proof of (2) gives existence of a positive gain without estimating its size. These are local growth statements for the genuine extremal quantity in [Erdős problem 142](https://www.erdosproblems.com/latex/142). A companion [note on residue sampling](ResidueSampling.md) identifies the worst-pair obstruction in the earlier counting argument.

## An exact interval construction

For $a\ge b\ge1$ there is a lower inequality
$$
 R(2a+b-1)\ge R(a)+R(b). \tag{3}
$$
Put optimal sets in the zero-based intervals $[0,a-1]$ and $[2a-1,2a+b-2]$. The distance between the two intervals is at least $a$. In a progression crossing the gap, one adjacent pair would be in a single interval and have distance at most $a-1$, while the other would have distance at least $a$. We also use the elementary upper inequality $R(x+y)\le R(x)+R(y)$.

For $n\ge12$ set $C=\lfloor(n+1)/3\rfloor$, $A=\lfloor C/2\rfloor$, $B=\lfloor(3A-1)/2\rfloor$ and $D=3A-1$. Put $M=R(n)$, $H=R(2n)$, $d=H-M$. The following applications of (3) use integer lengths throughout:
$$
\begin{aligned}
 R(D)&\ge 2R(A), &R(n-C)&\ge R(B)+R(A),\\
 H&\ge 2R(n-C), &H&\ge R(n-B)+R(D),\\
 H&\ge R(n-A)+R(C).
\end{aligned}
$$
For the domain checks, $C\le 2A+1$, $3A\le2B+2$, $3C\ge n-1$, and $2B+A+C-1\le n$. For the last inequality use $2B\le3A-1$, $2A\le C$ and $3C\le n+1$. The displayed floors also give $B\ge A$, $n-B\ge D$ and $n-A\ge C$ for $n\ge12$.

Subadditivity at $n=(n-B)+B$ and $n=(n-A)+A$ gives $R(D)-R(B)\le d$ and $R(C)-R(A)\le d$. Thus $R(n-C)\ge3R(A)-d$. Using the third split $n=(n-C)+C$,
$$
 M\le R(n-C)+R(A)+d
   \le \tfrac43R(n-C)+\tfrac43 d
   \le \tfrac23(M+d)+\tfrac43d .
$$
This is (1). The accompanying Lean file proves (3) and (1) for $n\ge12$ for mathlib's actual finite Roth number. The Python verifier enumerates free sets through length 22 and checks $0\le n<12$. Its recurrence tests every pair of older points that could make a progression ending at the newly added site.

## A flat interval would force another at half the value

To pass to real scales, consider $f_N(t)=R(\lfloor tN\rfloor)/R(N)$ for $t\ge0$. Along every sequence $N\to\infty$ there is a subsequence converging uniformly on compact intervals to a continuous nondecreasing $f$ with $f(0)=0$, $f(1)=1$. Here are the details. The functions are bounded on compact intervals by subadditivity. For $|t-s|\le\delta\le 1/4$, their difference has magnitude at most $R(\lceil\delta N\rceil)/R(N)$. The digit inequality $R(2wv)\ge R(w)R(v)$ bounds this quotient by $1/R(\lfloor1/(4\delta)\rfloor)$ once $N\ge1/\delta$. The digit construction takes $x+2wy$ with $0\le x<w$ and $0\le y<v$. The low second difference is smaller in magnitude than $2w$, so both digits of any progression must themselves form progressions. Since $R(m)\to\infty$ (powers of two already suffice), diagonal extraction on the nonnegative rationals and this modulus give the asserted uniform convergence. [Lean proof of the digit inequality](RothHeight.lean)

The two interval inequalities now become
$$
 f(x+y)\le f(x)+f(y),\qquad
 f(x+y+\max(x,y))\ge f(x)+f(y)\qquad(x,y>0).
$$
The errors from rounding are at most a bounded number of sites before division by $R(N)$. Also $f(t)>0$ for $t>0$ by subadditivity and $f(1)=1$.

Suppose $f$ is identically $H$ on $[a,b]$, with $3a/2<b<2a$. Then it is identically $H/2$ on
$$
 [2a-b,\ b-a]. \tag{4}
$$
For $z$ strictly between these endpoints, both $z$ and $a-z$ are less than $b-a$. The two inequalities give $f(z)+f(a-z)=H$. For sufficiently small $h>0$, $a+h+\max(z+h,a-z)<b$. Thus $f(z+h)+f(a-z)\le H$, forcing $f(z+h)=f(z)$. The same reasoning on the left, or the equality $f(z)+f(a-z)=H$ and right constancy at $a-z$, gives left constancy. The open interval is connected. Its constant value is $H/2$ by taking $z=a/2$. Continuity includes both endpoints.

For an explanation of the golden ratio, take $b=\varphi a$, where $\varphi=(1+\sqrt5)/2$. Transformation (4) divides both endpoints by $\varphi^2$ and the value by two. A persistent plateau would therefore give values $2^{-s}$ at scales $\varphi^{-2s}$ after normalizing $a=1,H=1$. The digit inequality and a Behrend bound give $f(t)\le t\exp(O(\sqrt{\log(1/t)}))$ as $t\downarrow0$, which contradicts those values because $\varphi^2>2$. The following finite computation gives the claimed fixed dilation slightly below $\varphi$ without using an asymptotic Behrend estimate.

## An explicit finite obstruction

If (2) failed, monotonicity would give a sequence $N\to\infty$ with $R(\lfloor\lambda N\rfloor)/R(N)\to1$. Its limiting profile would be identically 1 on $[1,\lambda]$. Write $u=1/F_{171}$. The endpoints of this interval are $F_{171}u,F_{172}u$. For each odd $i=171,169,\ldots,5$ the ratio $F_{i+1}/F_i$ is strictly between $3/2$ and $2$. The two endpoints in (4) become $F_{i-2}u,F_{i-1}u$. After 84 steps this gives $f(2u)=2^{-84}$.

Set $q=\lfloor F_{171}/4\rfloor$. Since $2q(2u)\le1$, applying the digit inequality to $q$ and $\lfloor2uN\rfloor$ then taking limits gives $1\ge R(q)f(2u)$. Yet $R(q)>2^{84}$. To verify this last strict inequality, take all 15-digit vectors with digits $0,\ldots,108$ in base 217. Their encoded values lie in an interval of $(217^{15}+1)/2\le q$ integer sites. No carry is possible in a midpoint equation. Among the $1+15\cdot108^2$ possible squared norms of a digit vector, some layer has at least
$$
 \left\lceil\frac{109^{15}}{1+15\cdot108^2}\right\rceil
 =20{,}818{,}825{,}107{,}809{,}855{,}127{,}467{,}922
 >19{,}342{,}813{,}113{,}834{,}066{,}795{,}298{,}816=2^{84}
$$
points. Equal-norm vectors with one the midpoint of two others must all be equal by strict convexity. This is the classical sphere construction. [Behrend-type constructions](https://arxiv.org/abs/2406.12290)

The verifier also checks $F_{172}^2-F_{172}F_{171}-F_{171}^2=-1$, so $\lambda<\varphi$. The contradiction rules out the proposed limit and proves (2). For reproduction run `python3 check_roth_growth.py`. The size of $c$ in (2) and the all-length behavior of $R(2n)/R(n)$ beyond the bounds given here are undetermined by this argument.
