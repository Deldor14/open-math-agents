# A finite doubling inequality for Erdős #142

For every k ≥ 4 and every natural N, the maximum r_k on the one-based interval satisfies

    r_k(2N) ≥ r_k(N) + r_k(ceil(N/2)).
    2 r_k(2N) ≥ 3 r_k(N).

This includes k = 4, extending the range k ≥ 5 recorded in Left to Solve note 103490. For k = 4 and N = 2 the factor 3/2 is attained. These finite inequalities leave the full asymptotic equivalent open.

Take an extremizer A in [1,N] and an extremizer B in [1,ceil(N/2)]. Place the disjoint sets 2A and 4B−3 in [1,2N]. Residue 3 modulo 4 is absent, so an arithmetic progression of length at least four cannot have odd difference. A progression of even difference is confined to one parity. In the even layer it pulls back to A. In the odd layer its difference must be divisible by four, since every member is 1 modulo 4, so it pulls back to B. For the second inequality, splitting [1,N] into two intervals gives r_k(N) ≤ 2r_k(ceil(N/2)).

## Files

- ParitySplit.lean proves an exact odd/even decomposition of avoidance for every even progression length, using Lean core.
- UpstreamParity.lean identifies the run formulation with Set.IsAPOfLengthFree for every length greater than one.
- Doubling.lean proves both inequalities for Set.IsAPOfLengthFree.maxCard itself. The constructive proof in this file also covers odd k ≥ 5.

Verified with Lean 4.33.1 and formal-conjectures commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53 (FormalConjecturesForMathlib.Combinatorics.AP.Basic). The three files use no placeholders. The axiom audit on the two final theorems lists propext, Classical.choice and Quot.sound.

To reproduce, build the pinned upstream AP.Basic module first. From the directory containing these three files, with that upstream module and its dependencies on LEAN_PATH and the same directory also on LEAN_PATH, run:

    lean -DwarningAsError=true -o ParitySplit.olean ParitySplit.lean
    lean -DwarningAsError=true -o UpstreamParity.olean UpstreamParity.lean
    lean -DwarningAsError=true -o Doubling.olean Doubling.lean

## Prime-power dilation

For every prime p, integer h ≥ 0, progression length k ≥ p^(h+1), and N ≥ 0, the maximum satisfies

    r_k(pN) ≥ p r_k(N) − floor(r_k(N)/p^h).

For example, the guarantees at (p,k) = (2,8), (3,9), (5,5) are 7/4, 8/3, and 4 times r_k(N), respectively, with upward integer rounding. At k = p^(h+1) and N = p^h the formula gives equality. These examples establish sharpness of the uniform factor across the stated range, without asserting the optimal factor for each larger fixed k.

Expand each point of an extremal set into a full block of p consecutive integers. Delete the least occupied residue class modulo p^(h+1). Every progression whose step is not divisible by p visits the deleted class among its first p^(h+1) terms. A progression whose step is divisible by p projects back to a forbidden progression in the original set. The candidate uses at least the number of points in the displayed formula.

Additional file PrimePower.lean proves prime_power_dilation, initial_values and prime_power_sharp on the same upstream definition. With the preceding three files built and Mathlib.Combinatorics.Pigeonhole available, run

    lean -DwarningAsError=true -o PrimePower.olean PrimePower.lean

The dilation and sharpness theorems both report only propext, Classical.choice and Quot.sound.

## Quantitative variation in the interval length

LocalGrowth.lean gives a digit construction with base b ≥ 2m−1 and a finite relative increment estimate. For all k ≥ 3,

    (2m−1)H ≤ N  ⇒  r_3(m) (r_k(N+H) − r_k(N)) ≤ r_k(N).

BehrendModulus.lean bridges the one-based interval to Mathlib's zero-based Roth number and its certified Behrend lower bound. For m,N ≥ 1, the same hypotheses imply

    r_k(N+H)/r_k(N) ≤ 1 + exp(4 sqrt(log m))/m.

The coefficient tends to zero as m tends to infinity. The estimate is uniform in k ≥ 3. The digit proof fills positions b(x−1)+y with x in a k-AP-free set and y in a 3-AP-free set in [1,m]. Three consecutive residues satisfy the midpoint equation modulo b. Their small range makes it an ordinary equality. The three digits must coincide, forcing divisibility of the common difference by b.

RegularScales.lean bounds the number of exceptional geometric scales. For every integer b ≥ 2, length k ≥ 3, 0 < q < 1 and J ≥ 0, the number of exponents j < J with r_k(b^(j+1)) ≤ q b r_k(b^j) is at most

    4 sqrt(J log b)/(-log q).

In particular their fraction tends to zero as J tends to infinity. This is a density-one conclusion on exponents. Subadditivity gives the upper growth factor b at every step, while each slow jump multiplies the best possible final value by another factor of q. The Behrend bound at b^J limits how many such factors are possible. The estimate does not determine the pointwise asymptotic equivalent requested in Erdős #142.

After building PrimePower, build LocalGrowth.lean, BehrendModulus.lean and RegularScales.lean, in that order, with the same Lean flags. The additional Mathlib dependency is Mathlib.Combinatorics.Additive.AP.Three.Behrend. The final declarations relative_increment, explicit_ratio and slow_scale_count passed the axiom audit with propext, Classical.choice and Quot.sound.

## Shape of the whole profile on most geometric scales

Profile.lean strengthens the estimate for one jump to a simultaneous estimate for every x in a geometric interval. Put N=b^(j+w) and B=b^w. For fixed b≥2, w≥1, k≥3 and 0<q<1, count an endpoint as bad if there exists an integer x in [0,N] for which

    |r_k(x)/r_k(N) − x/N| > (1+1/B)/q − 1.

Among the J consecutive window starts 0 ≤ j < J, the number of bad endpoints is at most

    4 w sqrt((J+w) log b)/(-log q).

The same bound holds for windows with r_k(b^(j+w)) ≤ q b^w r_k(b^j). To make the profile tolerance as small as desired, choose w large and then q sufficiently close to 1. For any such fixed tolerance the fraction of bad exponents tends to zero. The result controls all x simultaneously and does not determine the size of r_k(N) itself.

For the proof set F(j)=log(b^j/r_k(b^j)). Interval splitting makes F nondecreasing; Behrend gives F(j)≤4 sqrt(j log b). Summing the window differences F(j+w)−F(j) cancels all interior terms, leaving at most w F(J+w). The deterministic block_profile lemma controls the error between the grid points. Build Profile.lean after RegularScales.lean; the axiom audits for slow_window_count, block_profile and uniform_profile_count are clean.

Density.lean removes the auxiliary window choices from the conclusion. For every b≥2 and every ε>0 there is a C(b,ε) such that, for every k≥3 and J≥1, at most C(b,ε) sqrt(J) exponents j<J have even one x≤b^j with profile error greater than ε. The constant is independent of k. The theorem profile_density_one explicitly proves that this count divided by J tends to zero. Build Density.lean after Profile.lean; both audited final theorems use only the three standard axioms listed above.

## Ordinary integer endpoints

Ordinary.lean proves a result on all positive integer endpoints with logarithmic weights. For ε>0 let E_k(ε) consist of N≥1 for which some integer 0≤x≤N satisfies

    |r_k(x)/r_k(N) − x/N| > ε.

There is a C(ε)>0, independent of k≥3, such that for every X≥2,

    sum_{N<X, N in E_k(ε)} 1/N ≤ C(ε) sqrt(log X).

In particular this exceptional set has logarithmic density zero. The proof transfers accuracy at a dyadic endpoint M to every N in its upper half. If the whole profile at M has error ≤δ≤1/4, the error at N is ≤8δ, since r_k(N)/r_k(M)≥1/4. Each bad dyadic block costs at most one unit of harmonic weight. Combine the geometric exceptional-count bound with the number of dyadic exponents up to X. The statement and limit are checked as logarithmic_mass_bound and logarithmic_density_one. Build Ordinary.lean last. This theorem gives neither an independent formula for r_k(N) nor a claim concerning every sufficiently large N.
