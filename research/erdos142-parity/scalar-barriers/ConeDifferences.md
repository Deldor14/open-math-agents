# A negative difference of the dyadic Roth densities at order at most three quarters of the index

Let uₖ=r₃(2ᵏ)/2ᵏ, where r₃(n) is the maximum size of an interval subset without a nonconstant three-term arithmetic progression. Put Δuₖ=uₖ−uₖ₊₁. There is an absolute constant C such that, for every sufficiently large integer T,

    Δʰuₖ < 0   for some T≤k≤C T^(7/2) and 1≤h≤3k/4.                       (1)

The earlier [recurrence argument](NegativeDyadicDifferences.md) gave a window of order T⁴ log T and any fixed slope greater than 3.41902. The new proof uses a binary tree cut off at its admissible boundary, an integer polynomial with two nonreal conjugate roots, and the denominators of its polynomial solution. The estimates on r₃ used here are Behrend's lower bound and Theorem 1.4 of Raghavan's v3 preprint. [Behrend](https://doi.org/10.1073/pnas.32.12.331) · [Raghavan](https://arxiv.org/html/2603.27045v3#S1)

## Binomial coefficients inside a cone

Write Aₖ=2ᵏuₖ and let the linear functional L on real polynomials be given by L(xᵏ)=Aₖ. Write y=x/2 and z=1−y. At an initial index K, a word with i letters y and h letters z has weight

    L(y^(K+i)z^h) = Δʰu_(K+i).

A node has weight equal to the sum of its two children. Suppose these weights are nonnegative for T≤K+i≤J, h≤α(K+i), with α=3/4. Start at K≥T+2 and stop a node if splitting would put either child outside the cone, or once the chosen depth N is reached. Assume K+N≤J. All leaves have nonnegative weight and their sum is u_K.

For any i+h=N with h≤αi, at least binom(N,h)/N words ending at (i,h) reach depth N. To see this, view each word cyclically and cut it at a maximum of the partial sums that give increment i on a z and −h on a y. The total is zero. The rotated word stays below the chord of its endpoint, so each prefix with coordinates (i',h') satisfies h'≤(h/i)i'≤αi' when i>0. The reserve αK≥1 allows both children at every internal prefix to remain in the cone. Any good word has at most N preimages when the position of the chosen cut is retained. This also covers periodic words. The case i=0 can occur here only at depth zero.

Since one tree works for all endpoints, summing the leaf weights gives, for any set of these endpoints at depth N≥1,

    Σ binom(N,h) Δʰu_(K+i) ≤ N u_K.                                        (2)

This uses nonnegativity only at indices and orders inside the prescribed cone. The [finite Lean theorem](ConePathCredit.lean) proves (2) directly for differences of an arbitrary real sequence, including the rotation and common-tree count.

## A polynomial supported on these endpoints

Use the monic integer polynomial

    P(x)=x²³² (x−2)¹³² (x−1)¹⁶ (x²−3x+3)⁵.

Its ordinary degree is r=390. On y+z=1 its homogeneous expression of degree d=406 is

    2³⁶⁴ y²³² z¹³² (y²−z²)¹⁶ (y²+3z²)⁵.

Indeed x−1=y−z and x²−3x+3=y²+3z² there. Multiply by (y+z)¹⁶ to get the first difference of squares. Each coefficient of yⁱ z^(d−i), divided by binom(d,i), has absolute value ≤η=199/200. Nonzero terms have i≥232, hence d−i≤3i/4. Both bounds are finite integer comparisons: the coefficient at i=232+2j is 2³⁶⁴ times the coefficient of tʲ in (t−1)¹⁶(t+3)⁵ for 0≤j≤21. The [standalone verifier](verify_cone_polynomial.py) computes all 22 exactly. [ConeCyclotomic.lean](ConeCyclotomic.lean) verifies the polynomial identity, the 22 coefficients and the bounds on their magnitude and support in Lean 4.33.1.

For Pᵐ the same support constraint persists and every normalized coefficient is bounded by ηᵐ by Vandermonde convolution. Now choose K=T+2. For 0≤j<r and (K+j)+dm≤J, (2) implies

    |L(x^(K+j)Pᵐ)| ≤ 2^(K+j) dm ηᵐ u_(K+j) ≤ 2^(K+j) dm ηᵐ.

The left side is the absolute value of an integer. With M=⌈cT⌉ for a sufficiently large constant c, this bound is less than one for every m≥M. Thus these integers all vanish for M≤m≤m₁=⌊(J−K−r)/d⌋. The polynomials xʲPⁿ, 0≤j<r and 0≤n≤m₁−M, form a triangular basis through degree r(m₁−M+1)−1. This proves that P(S)ᴹ annihilates A at every consecutive index from K through K+r(m₁−M+1)−1, with S the forward shift. Extend the first rM terms from K by this monic recurrence. The extension is integral and agrees with A through at least K+r(m₁+1)−1. Choosing J a sufficiently large fixed multiple of a desired endpoint Z guarantees agreement through Z.

## The polynomial contribution of the root 2

Discard the zero root by starting at k₀=K+232M. The extended sequence w_l=A_(k₀+l) (through the range of agreement) obeys the recurrence

    (S−2)^v F(S),     v=132M,     F(x)=(x−1)^(16M)(x²−3x+3)^(5M).

There is a polynomial W of degree <v such that for k≥C₁T in the range of agreement,

    |uₖ−W(k)|≤exp(−c₁ k),         W(k) ∈ 2^(−k₀−v) ℤ.                    (3)

For the estimate, the generating function of w has denominator (1−2z)^v(1−z)^(16M)(1−3z+3z²)^(5M) and numerator of smaller degree. Its numerator coefficients are bounded by exp(O(T)) using the first O(T) terms w_l≤2^(k₀+l) and the coefficient norm of the denominator. Fix ρ strictly between 1/2 and 1/√3. The partial fraction at 1/2 has coefficients bounded by exp(O(T)), by the Cauchy bound on a fixed small circle there after multiplying by (1−2z)^v. Subtract it. The remaining function is analytic in |z|≤ρ and bounded on that circle by exp(O(T)), since the other poles have modulus ≥1/√3. Its l-th coefficient is at most exp(O(T))ρ^(−l). Dividing by 2^(k₀+l) gives the first bound in (3) once k≥C₁T. The removed partial fraction contributes precisely a polynomial after normalization.

For the denominator assertion, F(2)=1. Therefore there is an integer polynomial I with FI≡1 modulo (x−2)^v; one choice is the sum of (1−F)^j for 0≤j<v. Then w'=F(S)I(S)w is an integer sequence annihilated by (S−2)^v, while w−w' is annihilated by F(S). This is the same root-2 component by uniqueness of the two relatively prime recurrence factors. Expanding Sˡ=(2+(S−2))ˡ gives

    W(k₀+l) = Σ_(j<v) binom(l,j) ((S−2)^j w')₀ / 2^(k₀+j).

All integer samples with l≥0, and all their finite differences, consequently lie in the common lattice in (3).

## Extrapolation with nonnegative Newton coefficients

Let t₀=⌈C₁T⌉, increasing C₁ if necessary, and Z=⌈C₂ T^(7/2)⌉. For 0≤j<v put cⱼ=ΔʲW(Z−j). The cone hypothesis gives Δʲu_(Z−j)≥0 since v=O(T) and Z≫T. By (3) the discrepancy has absolute value at most 2ʲexp(−c₁(Z−j)). This is less than the lattice spacing 2^(−k₀−v). Thus cⱼ≥0, and a nonzero cⱼ is at least that spacing. The backward Newton expansion is exact,

    W(s)=Σ_(j<v) cⱼ binom(Z−s,j),       t₀≤s≤Z, s integral.

All summands are nonnegative. At s=t₀ we have W(t₀)≤2. Every index j≥1 with cⱼ>0 must therefore satisfy

    2 ≥ 2^(−k₀−v) binom(Z−t₀,j) ≥ 2^(−k₀−v) ((Z−t₀)/j)^j.

Since j≤v=O(T), this implies j≤C₃T/log T. Take X=⌈L T³ log T⌉ with L a large fixed constant. For every such j,

    binom(Z−t₀,j)/binom(Z−X,j) ≤ exp(2jX/(Z−X−v)) ≤ exp(C₄ L √T / C₂)

for all sufficiently large T. The constants C₁,C₃,C₄ can be chosen independent of L and of C₂≥1; the threshold on T can depend on them. The combination with nonnegative coefficients gives the same ratio bound for W(t₀) relative to W(X).

Behrend gives W(t₀)≥exp(−C₅√T), enlarging the constant to absorb (3). Raghavan gives W(X)≤exp(−c₅ L^(1/6)√T) for all sufficiently large T. Choose L first with c₅ L^(1/6)>2C₅, and then take C₂ large enough that C₄ L / C₂<C₅/2. The two bounds contradict the ratio estimate. This proves (1). In particular the use of the lattice in (3) eliminates the possible negative errors of the Newton coefficients and bounds the number of relevant orders. The recurrence and the analytic estimates are written arguments.

## Higher progression lengths

There is also a qualitative consequence for every fixed progression length s≥3. For uₖ=r_s(2ᵏ)/2ᵏ there are infinitely many k with Δʰuₖ<0 for some 1≤h≤3k/4. Indeed, eventual positivity throughout this cone would give the same permanent recurrence by fixing T and letting J tend to infinity. Its root-2 contribution W(k) must tend to zero by Szemerédi's theorem, so W is identically zero. The exponential error in (3) contradicts the lower bound r_s≥r₃ and Behrend's construction. This argument gives no uniform T^(7/2) window for s>3 from Szemerédi's qualitative theorem alone.
