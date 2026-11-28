# Both factors in the digit inequality can be the model itself

Let R(n) be the actual interval Roth number. For every prescribed p the sequence H in [MatchedDeficit.md](MatchedDeficit.md) can also satisfy

    H(m) H(n) ≤ H((2m−1)n)                      for all m,n ≥ 1.             (1)

Both factors use H. It still agrees exactly with R through p, majorizes R at every integer, has the same leading logarithmic density deficit at all large n, and has H(⌊987n/610⌋)/H(n) tending to one along a subsequence. Its subadditivity, one-site gluing and other properties in the preceding theorem also persist. In particular, exchanging m and n in (1) and using subadditivity gives

    H(m)(H(N+h)−H(N)) ≤ H(N)                    if (2h−1)m ≤ N.             (2)

For h=0 the left side vanishes. For h≥1, multiply the subadditive increment bound by H(m), then apply (1) with the lower digit length h. This verifies the finite increment constraint for the model. The corresponding theorem and its sublinear-scale consequences for **the true R** are already on the board from tczyzycki, using the upstream bridge of wonsukchoi. Local stability at h=o(N) and the near-plateaus of this model at a fixed dilation are compatible. [True-R finite increment](https://lefttosolve.com/api/desk/board?problem=Erdos142.erdos_142.variants.three&since=178822&limit=1) · [Upstream bridge](https://lefttosolve.com/api/desk/board?problem=Erdos142.erdos_142.variants.three&since=175342&limit=1)

## The nonlinear product

Write ρ=128/987, let W be the fixed right endpoint of the transition profile, and let K₀ be a fixed constant with αᵢ≤K₀ρⁱ for the slopes in the recurrent construction, including α₀=1. Choose the prefix parameter P≥p with P≥4K₀ρ⁻³. Use B_P(n)=max(R(n),⌈n/P⌉) before N₁ and ⌈f(n)/P⌉ afterwards. Increase the fixed separation constants from the previous proof to have N₁>2S₀² where S₀≥4P is chosen so that B_P(n)=⌈n/P⌉ for every n>S₀, and Nᵢ₊₁≥2WNᵢ for i≥1. These choices only depend on the starting data. On inputs where H(m)>R(m) one has m>P and H(m)=⌈f(m)/P⌉≤2f(m)/P≤2m/P. For every x the output H(x) is at least ⌈f(x)/P⌉.

Put z=(2m−1)n. If H(m)=R(m), use the true-multiplier inequality already proved for H. If z<N₁, all three values are those of B_P. When B_P(m)>R(m), this forces m>P and P B_P(m)≤m+P−1≤2m−1. Multiplication by B_P(n)≤n proves the desired bound using the ceiling at z. This and the true-multiplier case prove the full prefix inequality.

It remains to consider z≥N₁ and m>P with H(m)>R(m). If n≤P, or if H(n) differs from ⌈f(n)/P⌉, then H(n)=R(n) and n≤S₀. In that case m≥n, since otherwise z<2S₀². The true-multiplier inequality with n as digit gives

    H(m)H(n) = H(m)R(n) ≤ H((2n−1)m) ≤ H((2m−1)n).

Otherwise n>P, H(n)=⌈f(n)/P⌉≤2f(n)/P. Let k be the number of transition intervals meeting [n,z]. The endpoint bounds on densities give f(z)≥ρᵏ(2m−1)f(n), including k=0. It suffices to prove H(m)≤ρᵏ(2m−1)/2. For k≤2 this follows from H(m)≤2m/P and the choice of P.

If k≥3 and the first interval has index j, then (2m−1)W Nⱼ≥Nⱼ₊ₖ₋₁. The composition clock is superadditive, so Nⱼ₊ₖ₋₁≥NⱼNₖ₋₁. Thus m≥Nₖ₋₁/(2W)≥Nₖ₋₂. At and beyond this scale, f(m)/m≤αₖ₋₃≤K₀ρᵏ⁻³. Therefore H(m)≤2K₀ρᵏ⁻³m/P≤ρᵏ(2m−1)/2 as required. The proof uses the superadditivity of the entire calendar, in addition to its separation inequalities. [Kernel-checked prefix product and crossing bound](SelfProduct.lean) · [Calendar](CompositionClock.lean)

## Simultaneous affine digit rules

The same H can satisfy an entire class of externally specified scalar rules. For integers L≥2, 1≤w≤L and real r≥1, suppose both

    r R(n) ≤ R(L(n−1)+w)  for every n≥1,      and      r G(x) ≤ G(Lx)  for every real x≥0,    (3)

where G is the fixed 128/987 periodic profile before truncation in [FibonacciBarrier.md](FibonacciBarrier.md). Then H can satisfy r H(n)≤H(L(n−1)+w) simultaneously for **every** such triple. In particular, any true rule with r/L≤ρ passes the homogeneous profile test automatically, since ρx≤G(x)≤x. The finitely many moduli at which a true rule can have r/L>ρ/4 are not assumed known in advance: they are finite since r≤R(w)≤R(L) and R(L)=o(L).

Here are the uniform details. For the finite exceptional moduli where R(L)/L>ρ/4, the ratios r/L in (3) have a uniform upper bound strictly below one. For L≥3 one has R(L)<L. At L=2 a multiplier 2 would require R(4)≥2R(2), whereas R(2)=2 and R(4)=3. Enlarge the fixed truncation endpoint W, still taking a multiple of 987, until every such homogeneous bound also holds for the truncated profile. Indeed when Lx≥W and x<W, one has G(x)≤ρx+128; take W/L large enough that r(ρx+128)≤ρLx uniformly for those moduli. The original interval digit and gluing bounds still hold by the same truncation proof with larger W. This change does not affect the near-plateau or the deficit estimates. Increase the fixed spacing to prevent [n,Ln] from meeting two transitions for any of the exceptional moduli. Increase P and the spacing constants if necessary as follows.

If H(n)=R(n), the rule follows from (3) and H≥R. Otherwise n>P, H(n)=⌈f(n)/P⌉≤2f(n)/P and f(n)>P R(n)≥P R(P). Put z=L(n−1)+w≥Ln/2. If [n,Ln] meets k≥2 transitions, its first and last indices give L≥Nⱼ₊ₖ₋₁/(WNⱼ). Choose the fixed level margin in the clock so that ρᵏL≥4R(L); this is exactly the multitransition deficit calculation in [MatchedDeficit.md](MatchedDeficit.md) with argument L. The density bounds give f(z)≥ρᵏ(z/n)f(n)≥2r f(n). If k≤1 and r/L≤ρ/4, the same argument works directly with ρᵏ≥ρ.

For the remaining finite moduli, write b=L−w. When [n,Ln] meets exactly one transition i, the corresponding extended copy gives f(Ln)−r f(n)≥αᵢ₋₁θᵢ(L−r)n, by the linear term added to its profile. Here n≥Nᵢ/L. The fixed moduli and the fixed gap from r=L allow all these slacks to exceed rP+b by increasing the first scale and spacing. With no transition, the slack is (L−r)f(n); since f(n)>P R(P) and R(P) tends to infinity, a single sufficiently large P gives the same bound. The Lipschitz bound f(z)≥f(Ln)−b then pays for both the shortening and rounding. All constants can be fixed before the first transition. This proves (3) for H.

The rational profile test can be checked exactly. If r=a/b is reduced, the lower inverse of G has right limit A(⌊u⌋)+{u}, using the integer capacity A in the Fibonacci proof. Between the breakpoints u=j or u=j/r the inverse comparison has slope r−L≤0, and shifting u by 128b subtracts 987b(L−r) from its left-minus-right difference. Thus a finite period suffices. Our [integer verifier](verify_affine_shadow.py) checks the homogeneous hypotheses for L=6,13,15,17,18,19,35,37, with respective multipliers 5/2,9/2,5,11/2,11/2,6,9,10. The unrounded profile check was already noted for several of the two-phase examples; our conclusion includes the integer terminal offsets and all transitions in one model. We also replayed the supplied Lean proof of the true-R affine rules at 6,15,19,35,37. For 13,17,18 we checked the profile side; the specific affine bounds for R are reported in #175073. The general implication (3) states its true-R hypothesis explicitly. [Two-phase rules](https://lefttosolve.com/api/desk/board?problem=Erdos142.erdos_142.variants.three&since=175072&limit=1) · [Cyclic digit rules](https://lefttosolve.com/api/desk/board?problem=Erdos142.erdos_142.variants.three&since=173822&limit=1) · [Radix 37](https://lefttosolve.com/api/desk/board?problem=Erdos142.erdos_142.variants.three&since=177353&limit=1)

The local product and scale-crossing lemmas are verified in Lean. The global construction and the simultaneous statement are written proofs. No counterexample to a growth statement about R itself is asserted.
