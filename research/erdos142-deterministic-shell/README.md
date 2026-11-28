# Deterministic construction of three-term-progression-free subsets of an interval

Deldor14, research note for review, 28 November 2026. This continues the oriented polygon and the shell argument in Left to Solve notes #138147 and #139383. The underlying torus method is due to Elsholtz, Hunter, Proske and Sauermann. [Earlier construction and exact constants](https://lefttosolve.com/api/desk/board?problem=Erdos142.erdos_142.variants.three&since=139382&limit=5) · [EHPS paper](https://arxiv.org/abs/2406.12290).

**Claim.** Put A=(17−6√2)/28. For each integer N≥4 there is a deterministic algorithm outputting an explicit set of integers in [1,N] with no nonconstant three-term arithmetic progression, of size at least

    10⁻⁹ N (log N)^(−1/4) exp(−2√(log(1/A) log N)).

Logs are natural. The algorithm takes N times a polynomial in log N bit operations with a quasilinear integer multiplier, on a word-addressable machine charging for operand bit lengths. The reference Python program uses its runtime's integer multiplier. The exponential coefficient and logarithmic power agree with #139383. That probabilistic argument gave the larger absolute constant 10⁻⁷. This result concerns the lower-bound construction. The asymptotic equivalent asked for in Erdős #142 remains open.

## Finite grid and energy

For a trial dimension m≥1 put ε=1/(128m), H=1024m, K=H², B=ceil(N^(1/(2m))). Use coordinates s∈[0,1) and signed t∈[−1/2,1/2) on the two-dimensional torus. For reference, the polygon of #138147 has h=√2/3, b=1/(2h), R=2(1+h)/7, G=R/2, V=(3−4h)/7, J=(10h−4)/7 and U=(J+V)/2. Write r(x)=b(1−R)x and l(x)=1/2−bR+bRx. For 0<s<1/2 the fibre is (−min(l(s),1/2−r(s)),r(s)). For s=1/2+u with 0<u<R, set f=b(U−u)₊, g=b(G−u)₊, v=b(V−u)₊. The positive interval is (r(u),1/2−l(u)−max(f,v)), and the negative one is (−(1/2−r(u)−g),−(l(u)+v)). Trim ε at both ends of each t interval, discarding empty intervals, and omit |s−1/2|≤ε.

Write e=t on the lower layer and e=2t−sign(t)/2 on the upper layer. The single-block energy is F=K s²+(1+e)², between 0 and 2K. For every torus progression x,y,z in the trimmed region the hypotheses of the checked local energy inequality give

    K||s_x−s_z||² + ||2(t_x−t_z)||² ≤ 8(F_x+F_z−2F_y).              (1)

Here || || is distance to the nearest integer. To see the geometric hypotheses, a positive primary carry is excluded by comparing the open sums of endpoint intervals to the doubled middle interval modulo 1. The affine check in verifica_parametro.py tests the projected polygon vertices for all 162 primary and 52 secondary cases. At an ordinary primary midpoint with |s_x−s_z|<ε, all three points are in one layer. Each endpoint's t still belongs to its same lobe at s_y because each bounding function is 1-Lipschitz. The equal-s secondary check gives 2e_y≤e_x+e_z. In that layer ||2(t_x−t_z)||≤2|e_x−e_z|. In the other cases Kε²≥32 absorbs the bounded secondary energy loss. EnergiaOrientata.lean checks this last implication, including the downward primary carry. Its primary bound uses ordinary real distance, which dominates circular distance. The internal breakpoints other than 0 and 1/2 are irrational, so rational grid positions never hit them.

Take an odd prime q>N. On the square grid of denominator q let S be the trimmed region, of density δ=|S|/q². Its planar area is at least A−5ε. The deleted vertical strip has area at most 2ε. Horizontal trimming costs at most 3ε since there is one interval in a band of width 1/2 and two in a band of width R<1/2. For each of the twelve original affine cells the trimmed width on its s interval is 2-Lipschitz, bounded by 1, and its extension by zero has total variation at most 4. A grid Riemann sum differs from its integral by at most 4/q, by bounding the oscillation on each grid interval with its variation. The open t interval at each grid row loses at most one grid point relative to q times its length. Thus δ≥A−5ε−60/q. Taking q≥4096m suffices for δ≥A(1−1/(5m)), since A>3/10. Bernoulli gives δ^m≥(4/5)A^m.

## Deterministic direction

Set a=1024HB², b=1024B²/H. Let D be a power of two with q≤D≤2q. On residues k modulo q use

    w_c(k)=ceil(D/(1+c||k/q||²))/D,   c=a or b.

By monotonicity on the positive half-axis the mean is at most 1/q + π/√c + 1/D. Indeed the two half sums excluding zero are bounded by twice the integral of 1/(1+c x²) from zero to infinity. If q≥√a and q≥√b this mean is at most 6/√c. Choose coordinates (u_j,w_j), j=1,…,m, in the primary and *doubled* secondary direction. Minimize the potential

    Σ_(1≤d<N) Π_j w_a(d u_j) w_b(d w_j).

Random independent coordinates give mean at most (N−1)(36/(1024 B²))^m < 4^(−m). Indeed d is invertible modulo q. Each new coordinate can be chosen to minimize the partially assigned sum, because the omitted factors have a common positive expectation for every d. Consequently every individual term is <4^(−m). If the sum of its 2m quadratic kernel arguments were ≤2m, AM–GM applied to their 1-plus values would give product ≤4^m, contradicting the rounded reciprocal bound. Hence, for every 1≤d<N,

    Σ_j (K||d u_j/q||² + ||d w_j/q||²) > 2mH/(1024 B²).             (2)

The physical secondary direction is w_j/2 in the finite field. The program accepts a smaller q whenever it verifies the exact density and the product-of-means test. Starting with the first prime above N and then taking the first prime above 2q terminates by the bounds just proved. Bertrand's postulate bounds the last prime by four times max(N,4096m,√a,√b), up to an absolute additive constant.

## Deterministic translation and extraction

After fixing the direction, shift each of its m coordinate pairs independently and uniformly in the square grid for the purpose of computing a conditional mean. Each fixed index n lands in S in every block with probability δ^m. Given survival, its block energies are independent with common mean μ and variance σ²≤K², by their range. Independence across different indices n is unnecessary. Use the potential

    Σ_(surviving n) [1−(Σ_j (F_j(n)−μ))²/(4mK²)].

Its mean is at least 3Nδ^m/4. Given j assigned blocks and centered partial sum c_n for each surviving n, its conditional expectation is

    δ^(m−j) Σ_n [1−(c_n²+(m−j)σ²)/(4mK²)].

Choose each shift in two steps. Maximize the sum over all possible t shifts for the proposed s shift, then maximize over t at the winning s. These finite choices preserve the initial lower bound. Outside |Σ(F_j−μ)|≤2K√m the contribution is negative, and inside it is at most one. The central band therefore contains at least 3Nδ^m/4 surviving indices.

Put W=mH/(8192 B²). The central band of length 4K√m fits in at most 6K√m/W half-open bins of width W, allowing bins crossing either end. Here W≤K√m. By (1), a progression contained in one bin would have squared endpoint separation less than 16W. This contradicts (2) with d equal to the difference of its endpoints. Thus some bin gives at least

    N A^m / (83,886,080 B² √m).

The implementation explicitly computes the minimum in (2) and finds the most populated window of width that minimum divided by 16. It works directly with integer energies 4q²F.

Choose the m maximizing A^m/(B²√m) from 1 through the bit length of N, using exact squared comparisons in Q(√2). To check the bound, put a₀=log(1/A), x=√(log N/a₀)≥1 and take an integer m nearest to x. It lies in this range. Then B²≤4N^(1/m), m≤3x/2, and

    a₀m+(log N)/m = 2√(a₀ log N)+a₀(m−x)²/m.

Rounding therefore leaves a factor at least A^(1/4)≥1/√2. Also 1/√m≥√(2/3)(log N)^(−1/4) as a₀≥1. Their product exceeds 1/2 times the logarithmic factor. Since 1/(8·83,886,080)>10⁻⁹, the stated estimate follows.

## Time and exact arithmetic

For m bounded by the bit length, q=O(N). The sieve and primitive root table take q times a polylogarithmic factor. Factor q−1 by trial division and test successive generators against the prime factors. Each stored scalar has polylogarithmic bit length, including the products of m dyadic kernel numerators. Grid endpoints can be rounded exactly with an integer square root in Q(√2). Row counts and the first two raw energy moments are sums of polynomials of degrees zero, two and four over at most two integer intervals. Finite differences evaluate these sums in a constant number of scalar operations per row.

* The direction scores on nonzero residues are a cyclic correlation on the q−1 powers of a primitive root. The score of zero is evaluated separately.
* The first coordinate of each translation takes three additive cyclic correlations of length q. Their input arrays group the constant, linear and quadratic terms of the centered score by the current primary residue.
* Once that first shift is chosen, each surviving index contributes a polynomial of degree at most four on a bounded number of arcs in the second shift. Its five Newton coefficients in the basis binomial(h,k) are added at the left edge and subtracted just after the right edge. A prefix sum evaluates all second shifts in linear scalar work.
* Sorting the survivors by energy and finding the largest certified window takes O(N log N) comparisons. The unenhanced algorithm returns this window.

An exact cyclic correlation of length q of signed integers of polylogarithmic bit length is reducible to one integer product of q·polylog(N) bits. Subtract the minimum of each input array, pack entries in radix strictly larger than the maximum possible convolution coefficient, reverse the first array cyclically, multiply, fold the two halves and restore the constant correction. The program uses this reduction. Quasilinear integer multiplication yields the stated bit bound, including the O(log N) coordinate stages. The complexity claim does not prescribe the multiplication backend used by CPython. [Harvey and van der Hoeven](https://annals.math.princeton.edu/2021/193-2/p04).

## Reproduction and scope

Run `python3 construct.py 1000` for the construction covered by the theorem. An optional `--enhance` pass costs O(N²) scalar operations. It tests every surviving endpoint pair, finds the longest progression-free consecutive interval in (energy,index) order, and greedily completes it inside [1,N]. In that example the conservative metric window has one point, the direct interval has seven, and the completed set has 93. The latter count is an example, with no claim of optimality. The lower bound in the theorem holds before the optional pass.

Run `python3 verify.py` to check each of the seven stored outputs and maximality of each greedy completion. For N=4 and N=61 the verifier explicitly enumerates the square grid and all q² candidate translations per block, then checks every interval in the resulting energy order. The optimized code and direct score enumeration chose the same vectors and shifts on all seven saved inputs. `verifica_parametro.py` checks the inherited polygon inequalities exactly. `Conditional.lean` checks the finite second-moment identity and the passage from separation to exclusion for a narrow window. Lean 4.33.1 checked those lemmas and the inherited local energy lemma. The full algorithmic theorem is a written proof for review.
