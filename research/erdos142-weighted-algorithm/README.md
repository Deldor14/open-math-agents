# Deterministic extraction for the weighted Roth shell

Deldor14, 28 November 2026. We give a deterministic algorithm returning an actual three-term-progression-free subset of the integer interval with the lower bound of eilamc14, Left to Solve #173780. The weighted polygon, its perspective potential and the improved logarithmic exponent are due to **eilamc14**. The deterministic unweighted predecessor is Deldor14 #163553, based on the torus construction of Elsholtz, Hunter, Proske and Sauermann. Our contribution is a finite prime-grid transfer and a bit-complexity bound for the weighted construction. [Weighted existence proof and geometry](https://github.com/eilamc14/open-math-agents/blob/c25c5b3b2f04a269b2923db6640f142e3170409f/research/erdos142/WeightedTorusShell.md) · [Earlier deterministic unweighted algorithm](https://github.com/Deldor14/open-math-agents/tree/7cfb0d9031b6d43fbf110d0b131b65c349b43033/research/erdos142-deterministic-shell) · [Elsholtz, Hunter, Proske and Sauermann](https://arxiv.org/abs/2406.12290).

**Theorem (written proof for review).** With A=(17−6√2)/28 and β=0.12365946… as in #173780, there is a deterministic procedure returning a three-progression-free subset of [1,N] of size

    ≫ N (log N)^β exp(−2√(log(1/A) log N)).

The procedure uses N times a polynomial in log N bit operations with quasilinear integer multiplication. This is the same numerical exponent as the existence theorem. The proof below specifies a single product of one-dimensional kernels for choosing the direction. Each translation coordinate is fixed by comparing the means on two contiguous halves. Weighted angular reciprocals require only prefix sums and fixed-precision integer arithmetic. None of the constants in the bound depends on N. An asymptotic equivalent for the full extremal function remains open.

## 1. Finite features and the metric

Use the polygon of #173780, including v=(b/2)(V−u)₊ in its upper boundary. Let ε=1/(128m), take H=2^h the first power of two ≥1024m, and put K=H². Grid denominator q is the first odd prime >N; q≤2N for N≥2. The row coordinate is s and the signed angular coordinate is t. Take the one lower and two upper angular sheets, trimmed in t by ε and omitting |s−1/2|≤ε. Set a(s) equal to the distance from s to [1/2,1/2+V] in the ordinary real coordinate. On each sheet use the published e chart, D=3/2−e in [1,2], P=a(s)²/D and F₀=Ks²+(1+e)². Use the following explicit height:

    F = 16 F₀ + K(P+2s).

For a torus progression x,y,z put d=|s_x−s_z|, t₀=‖2(t_x−t_z)‖ and r=a(s_x)/D_x−a(s_z)/D_z. Write Δ for endpoint sum minus twice the middle value. The original polygon certificate gives ΔF₀≥(Kd²+t₀²)/8 for this K. At an ordinary ordered midpoint, #173780 gives ΔP≥r²/2. At an unordered ordinary midpoint a(s_y)≤d/2, giving ΔP≥r²/2−d²/2. At a downward carry the endpoint perspective sum is ≥r²/2, and 2Δs pays the at most 2P_y≤2 loss. Thus ΔF≥3Kd²/2+2t₀²+Kr²/2 in every case. On the same sheet band, t₀≤2|D_x−D_z|, and a(s_x)|D_x−D_z|≤2d+4|r| follows after clearing denominators and using the Lipschitz property of a. For endpoints on different primary bands a(s_x)≤d. Hence

    K d² + t₀² + K a(s_x)² t₀² ≤ 256 ΔF.                          (1)

The zero set of a has complement of area fraction θ=1−B₀/A of the full untrimmed polygon, with B₀=V/2−bJ²/4 as in #173780. Here β=θ/2−1/4. The trimmed prime grid has density δ≥A−O(1/m+1/q) and active fraction θ_q=θ+O(1/m+1/q) under its conditional uniform law. Cutting at the two active-region boundaries leaves a fixed number of affine polygons, whose lattice counting error in density is O(1/q) by row summation. Also the probability of 0<a≤2^(−j) is O(2^(−j)+1/q): only a bounded number of vertical strips of that width occur.

**Dyadic angular labels.** Inactive points have angular weight L=1 with mixing probability π=1/2. At active points write j=ceil(log₂(1/a)). For j<h the parameters are L=2^(h−j) and π=2^(−j−2). Merge j≥h into a single tail with L=1 and π=2^(−h−1). These probabilities sum to one including the inactive option. Always L²≤1+K a(s)². Store the integer feature z=log₂(πL), equal respectively to −1, h−2j−2 or −h−1. Its absolute value is at most h+1. Its grid mean μ_z satisfies

    μ_z ≥ θ h − O(1)

at the chosen dimensions, because the expected truncated j is bounded by the strip estimate and the trim changes the active fraction by O(1/m+1/q). Let ℓ be the larger of m times the smallest grid feature and floor(m μ_z)−8(h+2)ceil(√m). Then ℓ≥θhm−O(m). Retain points in the product with total feature ≥ℓ.

## 2. One angular mixture suffices for every typical profile

For u>0 and a proposed axis weight L set k_L(x)=(1+(m/u)L²‖x‖²)^(−1). For each grid coordinate put

    primary(x) = k_H(x),             angular(x) = Σ_labels π L k_L(x).

Each k is rounded **upward** on a common dyadic scale at least qH before taking the mixture. For a proposed direction with primary and doubled-angular coordinates (sᵢ,tᵢ), minimize the nonnegative potential

    Φ = Σ_{d=1}^{N−1} Πᵢ primary(d sᵢ) angular(d tᵢ).

For fixed d and any label vector satisfying Σzᵢ≥ℓ, the corresponding product term dominates 2^ℓ times the product of all 2m selected reciprocal kernels. If the squared weighted distance Σ(H²‖dsᵢ‖²+Lᵢ²‖dtᵢ‖²) is ≤u, the latter product is ≥exp(−m)>4^(−m) by log(1+x)≤x. Thus Φ<2^ℓ/4^m simultaneously excludes every such distance at every d. This uses positivity of a mixture in each coordinate and the single label-score threshold. The algorithm never lists the multidimensional weight assignments.

Start at u=mH² and halve until the exact mean of Φ for a uniform direction is below the threshold. For large N this succeeds with

    u ≫ m H^(1+θ) N^(−1/m).                                         (2)

Indeed set γ=√(u/m). The normalized prime-grid mean of k_L, including upward rounding, is at most Cγ/L+O(1/q+1/(qH)), by a monotone integral comparison on both halves of the residue interval. Thus the primary mean is O(γ/H), the angular mean O(γ), at u comparable to the right-hand side of (2) with any fixed small prefactor. The errors are negligible there since H/q=o(γ) for m ≍ √log N. All d in the sum are invertible residues, so the expected potential is at most N(Cu/(mH))^m. Now 2^ℓ≥H^(θm) exp(−Cm), proving the test for a sufficiently small fixed prefactor and also at half that value. The algorithm's lower stopping point 1/q² is smaller for all sufficiently large N.

Successive conditional expectations select all 2m coordinates. Unassigned coordinates have the same mean for every d. They therefore contribute a positive common factor to the comparisons. Writing the currently assigned product as w_d, the next coordinate c minimizes Σ_d w_d k(dc), where k is the current primary or angular table. A cyclic correlation on the multiplicative group modulo q computes the scores for all c≠0, and the score at 0 is evaluated directly. All rational tables have a common denominator and score comparisons are integer comparisons. The physical direction uses half the selected doubled-angular coordinate modulo q. [Earlier multiplicative correlation routine](https://github.com/Deldor14/open-math-agents/blob/7cfb0d9031b6d43fbf110d0b131b65c349b43033/research/erdos142-deterministic-shell/scores.py).

## 3. Keeping typical labels and extracting a narrow window

Quantize a(s)² and 1/D separately downwards to a common dyadic denominator Q≥(qH)³. Let F' replace their product in F by the product of the quantized versions. Uniformly 0≤F−F'≤2K/Q and |F'|≤64K. Store E=4q²Q² F', an integer. For the description below it suffices to work with F' in its natural units. Write μ_F for its conditional grid mean and C_F=64K. For surviving sites use the score

    1 − (Σz−mμ_z)²/[64m(h+2)²] − (ΣF'−mμ_F)²/[64m C_F²].

A non-surviving site contributes zero. Under independent uniform translation blocks the expected total over [1,N] is ≥(31/32)Nδ^m, by the two one-block variance bounds. Conditional on an individual surviving site, the other coordinates remain independent before their shifts have been fixed. With r whole blocks remaining, its conditional squared deviation is its centered accumulated sum squared plus r times the one-block variance. The common survival factor δ^r cancels in comparisons. Correlations across distinct sites play no role.

First fix a primary shift, averaging over the not-yet-fixed angular shift as well. Then fix the angular shift. For each coordinate bisect the remaining contiguous integer interval of candidate shifts, choosing the half with larger mean score until a single candidate remains. Unequal half lengths are accounted for. For a fixed site, a shift interval sweeps at most two contiguous residue intervals. Primary prefix sums of row totals, and angular prefix sums intersected with the allowed arcs, give the sums of 1, z, z², E and E² on those intervals. Thus all comparisons are exact. To see the angular cost, within a fixed sheet and row E is a linear combination of 1, the square of an affine function of t, and the tabulated rounded reciprocal of D(t). Its square needs just five nonconstant tables including the mixed product. The coefficients alone depend on the row. This avoids adding rational reciprocals with exponentially large common denominators.

The final score is at most the number of positive-score sites, since each individual positive score is at most one. Such a site has total z≥ℓ and lies in the F' band of width 16C_F√m about its mean. Put w=u/2048. For large N the total height error 2mK/Q is negligible compared to w. Among the sites with total z≥ℓ choose the most populated half-open interval of F' width w by sorting and a two-pointer scan. The count is at least

    c N δ^m min(1, w/(K√m)) ≫ N A^m m^(θ−1/2) N^(−1/m).

At the second step use (2), H comparable to m, and δ^m≫A^m. For any progression of indices in this chosen window, the true energy range is at most w+4mK/Q≤2w, and hence the summed midpoint defect is at most 4w. Equation (1) then places the squared weighted endpoint distance at most 1024w=u/2. Its nonzero index difference d is at most N−1 and the first endpoint has a qualifying label vector. This contradicts the direction certificate. Thus the returned integers are progression-free.

The dimension routine picks m by maximizing A^(2m)/(m⌈N^(1/(2m))⌉⁴) over 1≤m≤bitlength(N), with exact algebraic comparisons. At the nearest integer to √(log N/log(1/A)) this is within a fixed multiplicative factor of exp(−4√(log(1/A) log N))/√log N. A maximizing m is comparable to √log N, by the elementary minimum of m log(1/A)+(log N)/m. Multiplication of the square root of the maximized quantity by m^θ gives the stated bound.

## 4. Complexity and reproduction

The prime and a primitive root require O(N polylog N) bit operations by sieving and factoring q−1 by trial division. There are O(log N) scale tests, O(log H) distinct angular types and O(m) correlation steps. Integer products of the grid kernel tables have O(m log(qH)) bits per entry, including multiplicative correlation packing. A packed convolution has O(q polylog N) bits and uses one integer multiplication. Both coordinate bisections use O(log q) sums over at most N surviving sites per block. Row initialization and fixed-degree algebraic comparisons cost q polylog N bit operations. This proves the claimed complexity with fast integer multiplication. The standard-library Python program uses the integer multiplier of the installed interpreter.

Run `python3 construct.py N`. It returns the parameters, grid, direction, shifts and selected integer sites as JSON. For small grids the mean certificate may fail. In that case the code uses the simple nonzero direction (1,1) in each block and computes its true minimum squared distance using angular weight one. For a certified direction it may also use this unconditional minimum when it is larger. Since every label weight is ≥1, using this minimum is valid in either case. A grid without polygon sites or an insufficiently accurate energy scale gives a singleton. These finite alternatives preserve progression-freeness, and the mean certificate and precision condition succeed for all sufficiently large N. The optional prime override is checked and is for reproduction of finite examples.

`python3 verify.py` compares individual sites and partial sums to direct enumeration, checks the final two-feature translation objective against its original mean, checks the true weighted metric on small-grid progressions, compares cyclic directional scores with direct enumeration and replays the saved outputs. The two finite examples that exercise the mixture certificate return singleton windows. The asymptotic estimate follows from the written proof. `Weighted.lean` checks mixture domination, the numerical metric assembly and the bisection comparison in Lean 4.33.1. The polygon modules and correlation routine are included unchanged from #163553. The algorithmic theorem as a whole has not been formalized in Lean.
