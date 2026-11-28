# The variance barrier persists for arbitrary two-coordinate energies

Deldor14, 28 November 2026. This strengthens the [separable-energy result](https://github.com/Deldor14/open-math-agents/tree/c8d5b8876a5f40706ee271ec364aa579c9d314b7/research/erdos142-variance-barrier) for the oriented polygon of Deldor14 #138147/#139383/#163553, building on the Elsholtz–Hunter–Proske–Sauermann torus method.

**Theorem.** In the same polygon with uniform trim ε, let F be any finite Borel energy of finite variance σ² for normalized area. Suppose every ordinary-primary torus progression satisfies

    F(x)+F(z)−2F(y) ≥ λ(s_x−s_z)² + ||2(t_x−t_z)||²,     λ ≥ 0,

where ||·|| denotes distance to the nearest integer. Then σ ≥ c max(λ,ε⁻²) with an absolute c>0 for 0<ε≤1/65536. In particular changing the energy to one coupling the two coordinates still gives √λ/σ=O(ε) in the earlier one-shell Chebyshev certificate. The obstruction uses an entire interval of fibres.

**Four moving endpoints.** Write u=s−1/2 and I=[15/128,19/128]. Let A(u),B(u) be the positive and negative lower edges raised by 2ε. Let C(u),D(u) be the negative and positive upper edges lowered by 2ε. The closed intervals [A,D] and [B,C] are strictly inside the trimmed polygon. On I and a small neighbourhood of it all four edge curves are affine; indeed J<u<V and the positive upper edge there uses v, including on either side of the knot called F in the original verifier. Throughout, D=C+1/2. Put h=8ε/b with b=3√2/4 and κ=(1/32)². For each u in I the following are actual torus progressions. All the indicated doubled endpoint separations have distance at least 1/32 from the nearest integer.

* For a middle point at A(u), choose p in [23/64,23/64+1/512]. Endpoints at p and 2A(u)−p are strictly inside [A,D] and [B,C] at the same u.
* For a middle point at B(u), choose w in [1/32,1/24]. The two endpoints B(u)+1/2±w lie strictly inside [A,D] at the same u.
* Both C(u) and D(u) are midpoints of A(u−h) and B(u+h), with the endpoint horizontal coordinates shifted as indicated. Indeed A(u−h)+B(u+h)=2C(u)=2D(u)−1.

The exact affine endpoint and margin checks on the parameter rectangle are in `verify_envelope.py`. All inequalities are affine in u, ε, and p or w. The choice of representatives makes the circular-distance checks one-sided affine inequalities too.

**The largest endpoint energy.** Fix u. Inside either lobe the same-s, same-lobe ordinary midpoint inequality makes t↦F(1/2+u,t) midpoint convex. Its Borel measurability makes it convex: the ordinary measurable midpoint convexity theorem on an open interval applies. Hence the maximum on each of the two closed inner intervals is at an endpoint. Denote the maximum of the four values by M(u). In the first two progressions the two endpoints have energy at most M(u) and the defect is ≥κ. Neither A nor B can attain M. One of C,D therefore attains it. The last progression gives

    M(u−h)+M(u+h)−2M(u) ≥ κ.

Here M is defined using the same endpoints also just outside I. With k=floor(|I|/(8h)), a triangular sum gives the kh-step second difference ≥κ k² on the concentric subinterval of length |I|/4. All sample points for this amplification stay inside the concentric subinterval of length |I|/2.

**Bounding the envelope by the actual variance.** Subtract the block mean from F, and let g(u)² be the integral of F(1/2+u,t)² over that row of the trimmed polygon. Then ∫g²≤σ². On I, [1/8,1/4] lies inside the positive inner interval, hence M(u)≥−sqrt(8) g(u), by averaging F over that fixed interval and Cauchy–Schwarz. The energies at A and B are each bounded above by C₀ g(u) with an absolute C₀: integrate the first or second midpoint inequality over its displayed p or w interval. Each of the two endpoint maps is affine of slope ±1 in the integration variable, and each integration interval has fixed positive length. Using the last progression at a maximizing upper endpoint now bounds M(u) above by C₀(g(u−h)+g(u+h))/2 whenever u and its neighbours lie in I. Thus the L² norm of M on the concentric half of I is at most C₁σ. Possible exceptional rows of infinite g form a null set and do not affect the inequalities after integration.

The L² norm of the kh-step second difference of M on the concentric quarter interval is at most 4C₁σ by translation and the triangle inequality. Its pointwise lower bound κ k² gives σ≥c ε⁻². To get σ≥cλ independently, on the fixed rectangle I×[1/8,1/4] take a fixed horizontal step |I|/4 and equal vertical coordinates. On the concentric half of I the energy second difference is at least 4λ(|I|/4)², and its L² norm on this rectangle is at most 4σ. This proves the claim.

**Scope and checks.** Normalizing a positive secondary metric coefficient to one rescales F and λ. The proof covers every finite Borel energy with the stated pointwise metric control, including energies with no separation between the coordinates. It concerns the uniform trim and the specified volume-and-variance extraction. It neither bounds the actual largest AP-free set nor excludes using more detailed distributional information. The exact verifier uses the same two upstream Python files and command-line convention as `verify_barrier.py`. Three local lemmas in `FibreBarrier.lean` compile in Lean 4.33.1. The envelope variance theorem is a written proof for review.
