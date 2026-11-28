# The golden threshold with integer counts and any prescribed multiplicative tolerance

Use φ,Q,z,c and the digit inverse P from [GoldenRule.md](GoldenRule.md). Let R be the actual interval Roth number. Fix any finite family of triples (r,L,b), with integers L≥2, 0≤b≤L−1 and reals 1≤r<L, satisfying

    L P(1/r) ≥ 1,             rR(n) ≤ R(Ln−b) for every positive integer n.     (1)

For every fixed p and every positive g(n)→∞, there is an integer H with H(0)=0, H=R through p, H≥R everywhere and H(n)≤g(n)R(n) eventually. It is nondecreasing with increments at most one, is subadditive and satisfies the one-site join H(a)+H(b)≤H(a+2b−1) for 1≤a≤b. Each rH(n)≤H(Ln−b) holds at all positive integers, and

    liminf as n→∞ of H(⌈φn⌉)/H(n) = 1.                                         (2)

For a numerical pair passing only the profile test, the same construction enforces its rule eventually, allowing any of the specified terminal offsets. This covers the 1,024 archived numerical pairs without presupposing that an unreplayed archive entry is an actual extremal construction. A genuine fixed gain above one at φ for R is known. The [verified sphere](../subgolden/AllLengths.md) used in that proof fails the first condition of (1). The examples with *every* genuine digit multiplier, including the nonlinear model, in [RepeatedLosses.md](RepeatedLosses.md) have a different plateau dilation.

## Finite geometric profiles preserving each compatible homogeneous rule

For an integer s≥1 put M=2ˢ, w=Qˢ, ρ=M/w. Use the truncated binary capacity Aₛ(j): read the low s bits with weights Qⁱ and give the quotient ⌊j/M⌋ weight w. Then

    Aₛ(j)=j+Σ_{i=1}^s (Q−2)Q^(i−1) ⌊j/2ⁱ⌋.

The capacity is superadditive and Aₛ(j+1)≥Aₛ(j)+1. For 0≤i≤j it satisfies Aₛ(i+j+1)≤Aₛ(i)+2Aₛ(j)+1. Indeed, relative to the sum of the inputs and one, each binary floor can add at most a single carry. If 2ʰ≤j<2ʰ⁺¹, only indices through h+1 can carry. The sum of the first a coefficients is (Qᵃ−1)/Q using Q(Q−2)=Q−1. At a=min(s,h+1) this is at most Aₛ(j), by monotonicity and the capacity of the largest available bit. The case j=0 also follows directly.

On [Aₛ(j),Aₛ(j)+1] let Gₛ grow linearly from j to j+1, and then keep it constant through Aₛ(j+1). The two carry inequalities imply splitting and gluing for Gₛ by exactly the inverse argument of [FibonacciBarrier.md](FibonacciBarrier.md), which permits real capacity weights. Its density lies between ρ and 1, and Gₛ(x)≤ρx+M by periodicity. It is the identity until x=1.

The right-endpoint inverse here is Pₛ(t)=Aₛ(⌊t⌋)+{t}. For 0≤t≤M, Pₛ(t)≥P(t) because each fractional binary digit 2⁻ʲ in {t} is at least its geometric weight Q⁻ʲ. At each dyadic atom 2ᵏ, k≤s, both inverses equal Qᵏ. The proof of (1) in [ProfileDilation.md](ProfileDilation.md), decomposing the capacity into its dyadic atoms, works verbatim for these weights. Each homogeneous rule in our finite list passes at every s, since L Pₛ(2ᵏ/r)≥LQᵏP(1/r)≥Qᵏ.

There is an integer D, fixed independently of s, such that one can replace Gₛ(x) by ρx for x≥D w while keeping all these properties. The definitions meet at Dw by periodicity. Splitting for an output past Dw follows from the lower density bound. For gluing, if x≤y and x+2y≥Dw, then y≥Dw/3 and 2M≤ρy once D≥6. For a rule with Lx≥Dw and x<Dw, one has rGₛ(x)≤r(ρx+M)≤ρLx once D≥Lr/(L−r). Outputs and inputs on the outgoing line already satisfy all the rules.

Denote the truncated profile by Uₛ. The convex combination Uₛ,θ=(1−θ)Uₛ+θx has outgoing slope κ=ρ+(1−ρ)θ. All such profiles satisfy a common doubling gain Uₛ,θ(2x)≥(1+δ)Uₛ,θ(x) for a fixed δ>0 and all x>0. Normalize at x and use the result of eilamc14 for the entire continuous split-and-glue class at the dilation 2>φ. [Uniform doubling from the sharp threshold](https://github.com/eilamc14/open-math-agents/blob/512dda260bf02ae754b12997869c5f447a461d34/research/erdos142/GoldenRatioThreshold.md)

## Choosing scales from the true deficit

Fix an integer P₀≥p, to be increased below. Choose nondecreasing depths sᵢ→∞ which increase by at most one per stage, starting sufficiently large. They may tend to infinity arbitrarily slowly. Write ρᵢ=(2/Q)^sᵢ, θᵢ=ρᵢ²2⁻ⁱ, κᵢ=ρᵢ+(1−ρᵢ)θᵢ, α₀=1 and αᵢ=αᵢ₋₁κᵢ. Set Dᵢ=−log₂αᵢ. Then Dᵢ−Dᵢ₋₁=sᵢ log₂(Q/2)+O(2⁻ⁱ), and log₂(D Q^sᵢ)=O(1+sᵢ).

Let d(t)=log₂(2ᵗ/R(2ᵗ)) for integral t≥0. It tends to infinity, is nondecreasing and has increments at most one. Moreover d(t+h)−d(t)≤C(1+√h) uniformly in t, by the digit and Behrend bounds for the true R. Choose a sufficiently large fixed offset K≥log₂P₀+2 and let tᵢ be the first t with d(t)≥Dᵢ+K. Then Dᵢ+K≤d(tᵢ)<Dᵢ+K+1. The increment bound gives tᵢ−tᵢ₋₁≫sᵢ² for sᵢ large, and tᵢ≫(Dᵢ+K)² for Dᵢ+K sufficiently large. Put Nᵢ=2^tᵢ and Wᵢ=D Q^sᵢ. The supports [Nᵢ,WᵢNᵢ] are disjoint. The separations dominate any prescribed fixed multiple of Wᵢ₋₁/ρᵢ after taking the initial depth sufficiently large. Increase K to make the first support as late as needed. [Bounds on the true dyadic deficit](MatchedDeficit.md)

Use the function f(x)=αᵢ₋₁Nᵢ Uₛᵢ,θᵢ(x/Nᵢ) on each support, with the straight lines αᵢx between supports and x before the first one. It is nondecreasing and 1-Lipschitz. On [Nᵢ,Nᵢ₊₁) its density is between αᵢ and αᵢ₋₁. As in [FinitePrefix.md](FinitePrefix.md), use H(n)=max(R(n),⌈n/P₀⌉) before the first support and H(n)=⌈f(n)/P₀⌉ afterwards. The prefix equals the line ceiling for all n larger than a fixed S₀ by Roth's theorem. Take N₁>3S₀+3.

We give details for joining the profiles of different depths. At z=a+b or a+2b with a≤b and z≥N₁, let i be the last support start ≤z. Then b≥Nᵢ/3>Wᵢ₋₁Nᵢ₋₁ for i≥2. All terms belong to the i-th copy extended by its two lines, except possibly a. An earlier a has f(a)≥αᵢ₋₁a, enough for splitting. For gluing, in this case f(a)≤αᵢ₋₁Wᵢ₋₁Nᵢ₋₁ whereas f(b)≥ρᵢαᵢ₋₁Nᵢ/3. Thus f(a)≤δf(b)/2 by the stated separation. The surplus at z≥2b from doubling is at least δf(b)/2. If all arguments use the same extended copy, the linear summand supplies surplus αᵢ₋₁θᵢb. These surpluses divided by P₀ uniformly exceed three on taking K sufficiently large, by tᵢ≫(Dᵢ+K)², sᵢ≤s₁+i and Dᵢ≫i. This covers the one-site shortening and both ceilings. At a≤S₀ the possible prefix correction costs at most S₀, again absorbed by doubling. If z<N₁ the prefix lemma applies directly. Monotonicity and unit increments transfer at the join since both prescriptions agree immediately before N₁.

For the affine rules every [n,Ln] meets at most one support, by the spacing and the finiteness of the list. When H(n)=R(n), use the genuine rule and H≥R, proved below. Otherwise n>P₀ and H(n)=⌈f(n)/P₀⌉. With one support the tilt gives f(Ln)−rf(n)≥αᵢ₋₁θᵢ(L−r)n, where n≥Nᵢ/L. This exceeds rP₀+b for all the rules by the same size estimate. With zero supports the surplus is (L−r)f(n), and f(n)>P₀R(n)≥P₀R(P₀). Choose P₀ large enough to pay rP₀+b for the finite list; all subsequent scale choices are made after P₀. Lipschitz continuity pays the shortening b. For a pair known only numerically the very same bounds apply throughout the tail, where f(n) tends to infinity and the input always uses the line or profile ceiling.

## Pointwise comparison and the golden dilation

For Nᵢ≤n<Nᵢ₊₁, the true log₂(n/R(n)) differs from its dyadic floor-scale value by at most one and is at least Dᵢ+K−1. Since H(n)≥αᵢ n/P₀ this proves H≥R on the tail. The upper estimate on the true deficit is Dᵢ₊₁+K+2. Since H(n)≤2αᵢ₋₁n/P₀ there,

    0 ≤ log₂(H(n)/R(n)) ≤ Dᵢ₊₁−Dᵢ₋₁+O(1) = O(1+sᵢ+sᵢ₊₁).

The constants are fixed independently of how slowly the depths grow, after fixing P₀, s₁ and K. Choose the depths to grow sufficiently slowly that the last bound is at most log₂ g(n) for n≥Nᵢ and large i. This is possible already with the weaker n≥i, by using the tail infimum of g, and by imposing sᵢ₊₁≤sᵢ+1.

Before tilting, the i-th plateau of height Mᵢ=2^sᵢ has endpoints uᵢ=1+(Q^sᵢ−1)/(Q−1)=cQ^sᵢ+1−c and vᵢ=Q^sᵢ. We have φuᵢ=vᵢ+φ(1−c), a bounded overshoot. Choose nᵢ=⌈uᵢNᵢ⌉. Lipschitz continuity of the base profile shows that the relative gain of the untilted part at ⌈φnᵢ⌉ is O(1/Mᵢ). The relative contribution of the tilt is O(θᵢ/ρᵢ)=o(1). The final ceiling is negligible since αᵢ₋₁Nᵢ/P₀ tends to infinity. Monotonicity gives (2). The infinite splice and the adjustable tolerance are written proofs.
