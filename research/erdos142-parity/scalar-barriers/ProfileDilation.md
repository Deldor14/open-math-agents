# Eight tests decide every homogeneous digit rule for the Fibonacci profile

Let G be the continuous profile of [FibonacciBarrier.md](FibonacciBarrier.md). The seven-bit profile has weights w₀,…,w₇=1,3,8,21,55,144,377,987, period M=128 in value and width W=987. Let A be its integer capacity and put P(t)=A(⌊t⌋)+t−⌊t⌋ for real t≥0. For **every real gain r≥1** the least dilation L≥1 such that rG(x)≤G(Lx) for every x≥0 is

    B(r) = max_{0≤k≤7} wₖ / P(2ᵏ/r).                                          (1)

For r>64 this is just 987r/128. At r=64 the answer is 377. The large right jump at 64 reflects the exact level sets of this profile. The formula with k≤s holds at every depth s, using its own capacity and weights.

For example B(9)=1296/41, B(10)=275/8, B(17)=6409/81 and B(40)=1885/8. A cyclic set producing integer gain 17 at modulus at most 79, or gain 10 at modulus at most 34, would violate the profile condition. These are threshold tests for candidate constructions. They give no existence assertion for those cyclic sets.

## Proof

P(t) is the last x at which G(x)≤t. The lower inverse assigning the first point at which G reaches a level has right limit P(t). Thus the homogeneous inequality is equivalent to P(ru)≤L P(u) for every u≥0. In detail, if the inequality for G holds, G(x)≤ru for x at the last point with this bound, so G(x/L)≤u. Conversely suppose the inequality for P holds and G(Lx)<rG(x) at some x. Pick u strictly between G(Lx)/r and G(x). Then Lx≤P(ru)≤LP(u)<Lx. This also treats integer plateaus without identifying the two endpoints.

The floor formula P(t)=t+Σᵢ cᵢ⌊t/2ⁱ⌋ shows that P is superadditive and P(t)≥t, with equality on 0≤t<2. To test P(t)≤LP(t/r), write t=j+v with j integral and 0≤v<1. Expand j in binary below 2ˢ, allowing arbitrarily many copies of 2ˢ. For the resulting atoms d, one has j=Σd and P(t)=ΣP(d)+v exactly. By superadditivity P(t/r)≥ΣP(d/r)+P(v/r). Thus the dyadic tests and L≥r imply the inequality for all t. Conversely every atom is a permissible test. The atom 1 gives B(r)≥r, as P(1/r)=1/r. The decomposition and finite-test equivalence for the actual real floor sum are checked in Lean for arbitrary s. [Atom decomposition](ProfileAtoms.lean) · [Continuous finite test](ProfileDilation.lean)

Since t≤P(t)≤Wt/M and P(M)=W, all ratios in (1) are at most Wr/M. For r>M/2 the atom M attains this bound, since M/r<2. The special value at r=64 is obtained by the same eight rational tests.

## Published modular parameters

We compared every one of the 1,024 pairs (cardinality r, modulus L) in Jarek Wróblewski's BESTMOD.TXT against (1). Every pair satisfies L≥B(r). Among r≥3 the smallest ratios L/B(r) are 405/377 at (17,85), 296/275 at (10,37), and 1435/1296 at (9,35). The archive's warning about the reliability of some search records makes the distinction important: this calculation checks the listed numerical parameters. A verified digit witness at any listed pair, with its own terminal offset, therefore satisfies the profile-side hypothesis of the [simultaneous affine theorem](SelfConsistentDigits.md). No search for new digit sets was performed. [Primary archive and author's qualification](https://www.math.uni.wroc.pl/~jwr/non-ave/) · [Modular table](https://www.math.uni.wroc.pl/~jwr/non-ave/BESTMOD.TXT)

For reproduction run the [integer and rational verifier](verify_profile_archive.py) with a local copy of BESTMOD.TXT. The program verifies its hash, computes all eight inequalities for each pair, and reproduces the exact maxima by a second full-period calculation for each integer gain from 1 to 64.

## All depths at once

Each archive pair passes at **every** depth s, even though s can exceed the depth of the numerical record by arbitrarily much. So do the eight board rules in SelfConsistentDigits.md and the later pair (161,2679). The same program gives a finite certificate for each. For any k≤s, the denominator P_s(2ᵏ/r) is independent of s once s≥k, by the floor formula. At a trial index K write j=⌊2ᴷ/r⌋ and let I be the positions of its set bits. At index K+d, its capacity denominator is at least Σ_{i∈I}w_(i+d) because the integer j2ᵈ lies below 2^(K+d)/r. The differences

    E_d = L Σ_{i∈I} w_(i+d) − w_(K+d)

obey E_(d+2)=3E_(d+1)−E_d. Consequently 0≤E₀≤E₁ guarantees E_d≥0 for all d≥0. Testing earlier indices individually completes the certificate. Across the 1,024 pairs the largest necessary K returned by this procedure is 11. The certificate also covers the half-integer gains by rational arithmetic. The [mixed-radix sphere](../subgolden/AllLengths.md) that yields a genuine uniform gain for R has a different outcome. Its modulus 59³61⁹ and gain 2,303,115,151,489,024 violate the first atom at k=51. This explains how the finite archive and the genuine growth proof differ on this test.

[Board confirmation of the later (161,2679) witness](https://lefttosolve.com/api/desk/board?problem=Erdos142.erdos_142.variants.three&since=181213&limit=1).

## Exact terminal length in the two-input product

The previous scalar constructions and the regularly varying majorant can satisfy the sharper symmetric product

    H(m)H(n) ≤ H(S(m,n)),       S(m,n)=mn+(m−1)(n−1).

For R this is the familiar no-carry digit construction with base 2m−1. Extremizing digits u∈[0,m), v∈[0,n) give (2m−1)v+u in [0,S(m,n)). In a midpoint equation the difference of the two low-digit sums has magnitude at most 2(m−1)<2m−1, so both the high and low digits satisfy midpoint equations separately. The length S is symmetric, and 2S(m,n)−1=(2m−1)(2n−1).

For the integer models use the affine rule with L=2m−1, shortening b=m−1 and r=R(m). Its profile hypothesis was proved in FibonacciBarrier.md. Thus either input with H equal to R is covered, by symmetry, with m=1 or n=1 an identity. Otherwise both inputs use ⌈f/P₀⌉ with m,n>P₀, where P₀ is the large prefix parameter of the nonlinear construction. In particular H(m)≤2f(m)/P₀ and H(n)≤2f(n)/P₀. Put z=S(m,n)≥mn. If [n,z] meets k transitions, f(z)≥ρᵏ m f(n), where ρ=128/987. For k≤2 the choice P₀≥4ρ⁻² gives H(m)≤ρᵏm/2. For k≥3, z≤(2m−1)n implies m≥N_(k−2) as in the original crossing lemma, giving H(m)≤2K₀ρ^(k−3)m/P₀≤ρᵏm/2. This pays for rounding H(n) and proves the product across all stages, including in the model with unbounded repeated losses.

For the [regularly varying majorant](RegularMajorants.md), take its integer witnesses u≤x, v≤y in the definition of J. Write z=S(x,y) and h'=uv z/(xy). Since S(x,y)/(xy)=1+(1−1/x)(1−1/y) is nondecreasing in each variable, h'≥S(u,v)≥max(u,v). The split of the two logarithmic increments works with this h' exactly as before. This gives J(z)≥J(x)J(y). The concave hull preserves it because S(x,y) is affine separately in each variable, so independent finite mixtures retain the target mean. These two algebraic steps are [checked in Lean](CenteredProducts.lean). In particular the sublinear increment constraint holds for each such model at the sharpened threshold S(m,h)≤N as well, by subadditivity. The true-R sublinear stability was already proved independently on the board, and the fixed-dilation question concerns a different range of increments. [True-R result](https://lefttosolve.com/api/desk/board?problem=Erdos142.erdos_142.variants.three&since=178822&limit=1)
