# A sharp polynomial penalty for the interval independence number

Let $H=(V,\mathcal H)$ be a finite nonempty vertex set with unordered $k$-element edges, $k\ge2$, and let $r$ be its independence number. For nonnegative weights define
$$
 \Phi(w)=\sum_{i\in V}w_i^k+\lambda_k\sum_{e\in\mathcal H}\prod_{i\in e}w_i,
 \qquad \lambda_k=\frac{k^k}{(k-1)^{k-1}}-k .
$$
Then
$$
 \min_{\sum w_i=1}\Phi(w)=r^{1-k}.                                  \tag{1}
$$
The displayed coefficient is the smallest universal one. There is deterministic rounding from any nonzero input to an independent set of size at least $(\sum w_i)^{k/(k-1)}\Phi(w)^{-1/(k-1)}$. Each update removes a vertex from the positive support, preserves the total mass and never increases the cost. For fixed $k$ one can implement each step by testing at most $k$ candidates. Computing a globally optimal input remains a separate optimization problem.

For three-term progressions on $[0,N)$ the coefficient is $15/4$ and the minimum is exactly $1/r_3(N)^2$. [The complete cubic theorem in Lean](RothCubicRank.lean) uses the actual Mathlib function `rothNumberNat`. It includes the attained minimum for every $N>0$, rounding for every finite triple system, and sharpness of the coefficient. As an application to the [circle energy](RothCircleEnergy.md), at every $N$ the previous constant $16/27$ improves to one:
$$
                (N/r_3(N))^2\le E_3(N)\le18(N/r_3(N))^2 .          \tag{2}
$$
The lower bound with constant one also holds for every $k\ge2$, with the exponent $k-1$. Determining the growth of the minimum with $N$ is the remaining asymptotic question. For context, the graph case of (1) is the Motzkin–Straus formula on the complement graph. Exact hypergraph formulations using completely positive tensors provide another connection to polynomial optimization. [Chen, Huang and Qi](https://arxiv.org/abs/1609.07919).

## Replacing the weights of an occupied edge

Choose an edge whose weights $x_i$ are all positive. There is a positive level $t$ such that $\sum_{i\in e}\min(1,x_i/t)=k-1$, by continuity. Freeze every coordinate of size at least $t$. For each of the $m$ others put $u_i=x_i/t$, and put $u_i=1$ at the frozen positions. The deficits $1-u_i$ sum to one. Omit a single small position $i$ with probability $1-u_i$, set each of the other small positions to $t$, and leave all remaining weights fixed. The small weights sum to $(m-1)t$, so each output has the original mass.

Every coordinate retains its mean. A set of small positions $B$ survives together with probability $1-\sum_{i\in B}(1-u_i)\le\prod_{i\in B}u_i$ (the elementary union bound for independent events gives the inequality). Thus every other edge product has expected new value at most its original value. The chosen edge is killed in every output. The increase of the vertex cost, the same in every output, is
$$
 t^k\left(k-1-\sum_{i\in e} u_i^k\right)\le \lambda_k t^k\prod_i u_i
                 \le \lambda_k\prod_{i\in e} x_i.                   \tag{3}
$$
The simplex inequality in the middle is proved below. At least one output of positive probability has cost at most the original. Repeating and using Hölder on the terminal support $S$ gives $(\sum w_i)^k\le |S|^{k-1}\Phi(w)$. A uniform input on a maximum independent set attains (1). For a single edge on $k$ vertices, equal weights require $k+\lambda\ge k^k/(k-1)^{k-1}$, giving sharpness. For any coefficient strictly above $\lambda_k$, every global minimizer is uniform on a maximum independent set: any occupied edge would permit a strict improvement.

## The sharp simplex inequality for every uniformity

We show $\sum u_i^k+\lambda_k\prod u_i\ge k-1$ on $[0,1]^k$ with $\sum u_i=k-1$. For $k=2$ this is $(u_1+u_2)^2=1$. For $k\ge3$ take a minimizer. If a coordinate is zero all others are one, giving equality. Otherwise write $P=\prod_i u_i>0$. At every coordinate strictly below one, variation of two interior coordinates forces the same value of $h(u)=ku^{k-1}+\lambda_k P/u$. This function is strictly convex on the positive axis. There are at most two interior values. If there are two, $a<b$, stationarity gives
$$
 \lambda_kP=kab\frac{b^{k-1}-a^{k-1}}{b-a}>k(k-1)a^k .
$$
The smaller value occurs once: a transfer between two copies would have strictly negative second derivative $2k(k-1)a^{k-2}-2\lambda_kP/a^2$. Also there can be no coordinate at one in this two-value case. Transferring an infinitesimal mass from it to an interior coordinate requires $h(1)\le h(b)$ at a minimum, contradicting strict convexity and $h(a)=h(b)$.

With two distinct values we thus have $(a,b,\ldots,b)$. Put $t=a/b$ so $0<t<1$ and $b=(k-1)/(k-1+t)$. The quotient $(k-1-\sum u_i^k)/P$ is
$$
 F(t)=\frac{(k-1)(1+t/(k-1))^k-(k-1)-t^k}{t}.
$$
It is at most $F(1)=\lambda_k$. To see this, its polynomial expansion has positive coefficients in degrees $0$ to $k-2$ and a negative leading coefficient in degree $k-1$. One has $F'(1)=0$, either by differentiation or by symmetry at the equal-coordinate point on the fixed-sum hyperplane. Consequently $F'(t)/t^{k-2}$ is decreasing on $(0,1]$ and nonnegative there.

In the remaining case all $m$ coordinates strictly below one are equal, hence $m\ge2$ and each equals $1-1/m$. The quotient is
$$
 \lambda_m+m\big[1-(1-1/m)^{k-m}\big]\le \lambda_m+k-m\le\lambda_k.
$$
The first inequality is Bernoulli's. For the second, $\lambda_m-m=m[(1+1/(m-1))^{m-1}-2]$ is nondecreasing for integral $m\ge2$, as $(1+1/n)^n$ increases from two. This proves (3) on every face.

## Three-term rounding and the Fourier expression

For $0<x\le y\le z$ and $x+y\le z$, one can merge $x,y$ into a single coordinate chosen in proportion to their masses. The cubic cost increase is $3xy(x+y)\le3xyz$. If $x+y>z$, each of the three replacements has two equal coordinates $t=(x+y+z)/2$ and one zero. Omitting coordinate $x$ has probability $1-x/t$, and likewise for the others. In this case (3) is precisely Schur's degree-three inequality. Its slack multiplied by four is
$$
 4(x^3+y^3+z^3)+15xyz-(x+y+z)^3
 =3[(z-y)^2(z+y-x)+x(y-x)(z-x)] .
$$
These are the two steps used in the Lean proof. With $P(\theta)=\sum_{i<N}w_i e^{2\pi i i\theta}$, integration picks out $a+c=2b$. Every nonconstant edge occurs in both orders and every diagonal once. Hence the interval cubic to minimize can equivalently be written
$$
        \tfrac{15}{8}\int_{\mathbb T}P(\theta)^2\overline{P(2\theta)}\,d\theta
                     -\tfrac78\sum_i w_i^3 .
$$
All Fourier coefficients in this last program are nonnegative real weights summing to one. These are different variables from a nonnegative function in the circle energy comparison.

There is an algorithmic distinction between optimality and stationarity even for a single triple. At a coefficient $15/4<\lambda<6$, its uniform three-site point is a strict local minimum that has higher cost than a uniform independent pair. Indeed the Hessian on the zero-sum plane at the uniform point is $(2-\lambda/3)$ times the identity. If $\lambda>6$, every local minimum of any triple system has independent support. In an occupied edge move mass between its two smallest weights $x,y$, holding their sum fixed. The second derivative is at most $6(x+y)-2\lambda z<0$ where $z$ is the third weight. Uniformity on an independent support follows by strict convexity. Nonmaximal independent supports admit descent by adding mass at an unblocked vertex. Conversely, each uniform inclusion-maximal independent support is a strict local minimum in this range. At each outside vertex the directional cost of entering, net of mass removed from the support, is at least $(\lambda-3)/|S|^2>0$. More explicitly, by continuity all outside partial derivatives strictly exceed all support partial derivatives in a neighborhood. Moving outside mass back to the support there reduces cost, and the minimum restricted to the support is strict.

## A circle inequality at the actual length

For $f\ge0$ in $L^k(\mathbb T)$ set $J=\int f^k$, $L=\iint\prod_{j=0}^{k-1}f(x+jd)\,dx\,dd$. Choose independent uniform $x,d$ and use the $N$ weights $f(x+id)$. By (1), deterministically for these values, their mass to power $k$ is at most $r_k(N)^{k-1}$ times their cost. An index progression of step $s>0$ has expected product $L$, since $(x,d)\mapsto(x+id,sd)$ preserves Haar probability. Writing $a_{k,N}$ for the number of increasing nonconstant progressions, Jensen gives
$$
 (N/r_k(N))^{k-1}(\int f)^k
 \le (N/r_k(N))^{k-1}\!\iint\left(N^{-1}\sum_{i<N} f(x+id)\right)^k
 \le J+(\lambda_k a_{k,N}/N)L .
$$
The sum of $N-(k-1)s$ over positive admissible steps is bounded by the integral of its positive part over real $s\ge0$, giving $a_{k,N}\le N^2/[2(k-1)]$. We have $\lambda_k\le2(k-1)$: for $k=2,\ldots,7$ this follows by direct substitution, and for $k\ge8$ use $(1+1/(k-1))^{k-1}<e<11/4\le3-2/k$. This proves (2) and its general-$k$ lower bound. For three terms the coefficient of $NL$ in the upper expression is at most $15/16$. The comparison and the exact finite program leave the evaluation of the asymptotic open.

## Checks

The main Lean theorem `interval_minimum` proves (1) for the interval and $k=3$, including a witness for the minimum. Its proof uses support-decreasing rounding on arbitrary finite triple systems, with every other edge accounted for. The higher-uniformity simplex inequality and the Haar integral comparison have written proofs. [The exact verifier](check_roth_cubic_rank.py) checks 1,281 local rational weight patterns through uniformity eight, all 1,024 labelled triple systems on five vertices and 150 further hypergraphs against independent-set enumeration.
