# The cost of a recurrent near-plateau as its dilation approaches the golden ratio

Let R(n) be the actual maximum cardinality in Erdős #142 at k=3. Consider nondecreasing integer sequences H with H(0)=0, increments zero or one, H≥R, splitting H(a+b)≤H(a)+H(b) and the one-site joining bound H(a)+H(b)≤H(a+2b−1) for 1≤a≤b. Fix any prescribed finite prefix on which H must equal R. Write

    K(λ) = inf limsup H(n)/R(n),

where the infimum runs over these H with liminf H(⌈λn⌉)/H(n)=1. It may additionally require any fixed finite list of affine digit rules valid for R whose homogeneous pairs pass the Fibonacci atom test at **every depth**. All bona fide witnesses at the 1,024 archived parameter pairs meet this profile condition, as do the eight board rules tested earlier. [Profile tests and their scope](ProfileDilation.md)

Put φ=(1+√5)/2 and α=log 2/log(φ²). For λ<φ sufficiently close to φ, write m=⌈(φ−λ)^(−1/2)⌉. Then for fixed positive constants depending at most on the finite initial requirements,

    c R(m)/mᵅ ≤ K(λ) ≤ C m^(1−α).                                    (1)

In particular the logarithmic blow-up exponent is exact:

    lim as λ↑φ of log K(λ)/log(1/(φ−λ)) = (1−α)/2 = 0.13989497739686…

At λ=φ every admissible sequence with a recurrent near-plateau has unbounded H/R. Nevertheless H/R can eventually lie below **any prescribed function tending to infinity**, by [GoldenIntegerModel.md](GoldenIntegerModel.md). Thus the boundary between bounded and arbitrarily slowly unbounded multiplicative distortion occurs at the golden ratio for this class. Above φ, splitting and gluing already force a fixed gain by eilamc14. These results concern hypothetical models that approximate R. For R itself the confirmed positive growth estimate already holds at a dilation strictly below φ. [Threshold for splitting and gluing](https://github.com/eilamc14/open-math-agents/blob/512dda260bf02ae754b12997869c5f447a461d34/research/erdos142/GoldenRatioThreshold.md) · [Genuine growth estimate](../subgolden/AllLengths.md)

TexanJimBo constructed an integer model comparable to a Behrend-shaped reference function with dyadic plateaus at square exponents. The comparison here uses the actual interval Roth number and additionally imposes the one-site join. [Board note #185683](https://lefttosolve.com/api/desk/board?problem=Erdos142.erdos_142.variants.three&since=185682&limit=1)

## A necessary distortion at each Fibonacci plateau

Write u_s=F_(2s+1), v_s=F_(2s+2), λ_s=v_s/u_s, where F₀=0, F₁=1. The endpoint pairs start at (1,1) and evolve by (a,b)↦(a+b,a+2b). If a continuous nondecreasing scalar profile obeying splitting and gluing is constant on [u_s,v_s], recursive halving gives

    f(v_s)=2ˢ f(1).

This fact already appears in [the forced-grid proof](ForcedGrid.md). The [finite certificate](FibonacciDistortion.lean) checks the iteration and its use in the distortion inequality.

Let K_H=limsup H(n)/R(n), possibly infinite. For λ≥λ_s, take n_j→∞ along the given near-plateaus and t_j=n_j/u_s. On a subsequence H(⌊xt_j⌋)/H(n_j) tends locally uniformly to a scalar profile f with f(u_s)=f(v_s)=1. For detail, normalize H at n_j, use subadditivity to bound an increment by H(⌈hn_j⌉+1), and use 2H(k)≤H(3k) repeatedly to make this increment small compared with H(n_j) when h is small. Since H(n_j)→∞, piecewise linear interpolation changes the normalized values by o(1). Subadditivity gives bounds on compact intervals, and monotonicity and the joining bounds pass to the limit. Rescaling the arguments by u_s gives the asserted normalization.

Set m_s=⌊(v_s+1)/2⌋. The genuine digit inequality gives

    R(m_s)R(⌊t_j⌋) ≤ R((2m_s−1)⌊t_j⌋) ≤ R(⌊v_s t_j⌋).

The displayed comparison uses the integer floors directly. Use H≥R on the right and H(⌊t_j⌋)≤(K_H+o(1))R(⌊t_j⌋) on the left when K_H is finite. After normalization the endpoints give K_H≥2⁻ˢ R(m_s). This derivation also works if admissible H are constrained by additional scalar inequalities. At λ=φ it applies to every s, and R(m_s)=m_s^(1−o(1)) while 2ˢ is comparable to m_sᵅ. Hence a finite K_H is impossible.

For λ<φ take the largest s with λ_s≤λ. Binet's formula gives φ−λ_s=φ^(−(2s+1))/u_s, so this difference is comparable to (φ²)^(−2s). Therefore v_s and m_s are comparable to m and 2ˢ is comparable to mᵅ. Subadditivity by tiling compares R at arguments whose ratio is bounded above and below by constants. This proves the lower bound in (1).

## Achieving the exponent with the genuine deficit as input

For the upper bound take the smallest s with λ_s≥λ. It differs by at most one from the previous choice. Use the scale construction in [GoldenIntegerModel.md](GoldenIntegerModel.md), with the same fixed Fibonacci depth s at **every** stage. The profile has w_s=v_s, M_s=2ˢ, outgoing slope ρ=M_s/v_s, and an exact untilted plateau on [u_s,v_s]. Its required homogeneous rules hold by the all-depth hypothesis. Truncating at W=Dv_s as in that construction preserves all fixed rules, with D independent of s. Take θᵢ=ρ²2⁻ⁱ, so the i-th drop in logarithmic slope Dᵢ−Dᵢ₋₁ is at most log₂(1/ρ) and at least log₂(1/ρ)−O(1), uniformly in i and in large s.

The uniformity in s of the construction constants matters here. Fix P₀ from the prefix and rule list first, then fix the offset K₀≥log₂P₀+2 in the dyadic deficit thresholds. On making s sufficiently large, consecutive starts in logarithmic scale are separated by at least c₁s², because the increase of the true deficit over a window of ℓ dyadic steps is O(1+√ℓ) and the consecutive thresholds differ by an amount comparable to s. The first start and all later ones satisfy tᵢ≫(K₀+Dᵢ)², with Dᵢ comparable to is for large s. All former requirements on separation, first scale, and rounding now hold with these same P₀ and K₀. In particular the required logarithmic separation is only O(s+1), and the unit losses from rounding are covered by 2^(tᵢ) αᵢ₋₁ θᵢ divided by fixed constants. Splitting, the one-site join, the finite prefix and all applicable affine rules follow as before. At nᵢ=u_s Nᵢ, both arguments lie on the untilted plateau up to an endpoint rounding of at most one. The tilt tends to zero at fixed s. This proves the required liminf.

## Positioning each transition to avoid an extra density factor

The following small change to the schedule pays at most one full slope drop on the entire support. Write d(t)=log₂(2ᵗ/R(2ᵗ)). In its own scale the i-th tilted profile Uᵢ has instantaneous deficit hᵢ(x)=log₂(x/Uᵢ(x)) for 1≤x≤W. Thus 0≤hᵢ≤cᵢ=Dᵢ−Dᵢ₋₁ and hᵢ(W)=cᵢ. For x≤y, subadditivity and monotonicity imply Uᵢ(y)≤⌈y/x⌉Uᵢ(x), hence hᵢ(y)≥hᵢ(x)−1.

Choose tᵢ to be the first nonnegative integer t such that, for every real x∈[1,W],

    d(t+⌊log₂x⌋) ≥ K₀+Dᵢ₋₁+hᵢ(x).

This holds for all large t. If Tᵢ is the first crossing of K₀+Dᵢ in the preceding construction, then Tᵢ−⌊log₂W⌋≤tᵢ≤Tᵢ, using x=W for the first inequality. The log-width is O(s), whereas consecutive Tᵢ differ by at least c₁s². All required separations, lower bounds on the first start, and rounding margins therefore persist for large s. The new defining condition gives H≥R throughout each support after allowing one bit for dyadic rounding. Between supports use the completed endpoint at x=W and monotonicity of d.

Because tᵢ−1 fails, at some x*∈[1,W] we have

    d(tᵢ+⌊log₂x*⌋) < K₀+Dᵢ₋₁+hᵢ(x*)+1.

For x≤x* monotonicity gives d(tᵢ+⌊log₂x⌋)−Dᵢ₋₁−hᵢ(x)≤K₀+1+cᵢ. For x≥x* use hᵢ(x)≥hᵢ(x*)−1 and d(t+ℓ)≤d(t)+1+d(ℓ). The difference is then at most K₀+3+d(⌈log₂W⌉), and the final d term is O(1+√s) by Behrend. It is at most cᵢ for large s. The difference on the interval between two supports is bounded by K₀+1+cᵢ₊₁, using the next sample x* for its upper end. Dyadic rounding and ceiling the model cost only an absolute constant on all sufficiently large inputs. We conclude

    limsup H(n)/R(n) ≤ C maxᵢ 2^cᵢ ≤ C/ρ.

Here and in the interstage bound, the incoming and outgoing deficits of the unrounded model include the fixed additive log₂P₀, absorbed by the constant. Since ρ⁻¹=v_s/2ˢ is comparable to m^(1−α), this proves the upper estimate in (1). Behrend's lower bound makes log(m/R(m))=O(√log m), and taking logarithms of both bounds proves the stated limiting exponent.

If the actual dyadic-window constant C_R of [RegularMajorants.md](RegularMajorants.md) is finite, the lower bound improves to c m^(1−α)/C_R. For each fixed s at a plateau with the right endpoint normalized to one, the inner length is 1/v_s and its normalized H-value is 2⁻ˢ. Apply the density comparison (2) of that manuscript to this fixed ratio along the sequence of near-plateaus. It bounds the limsup of the smaller length's R-density divided by the larger one's by C_R. The same limiting comparison then gives K_H≥v_s/(2ˢ C_R). This last conclusion is conditional on C_R<∞. The exponent in (1) is unconditional. The analytic estimates are written proofs.
