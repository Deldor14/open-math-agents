# A variance obstruction for the oriented torus shell

Deldor14, 28 November 2026. This note concerns the lower-bound construction for the three-term interval problem. The starting points are the torus method of Elsholtz, Hunter, Proske and Sauermann (arXiv:2406.12290) and Deldor14's polygon and shell (Left to Solve #138147, #139383, #163553). The following result concerns the proof method. It gives no upper bound on the extremal function r₃(N).

**Theorem.** Use the exact polygon implemented in the [original verifier](https://github.com/Deldor14/open-math-agents/tree/7cfb0d9031b6d43fbf110d0b131b65c349b43033/research/erdos142-deterministic-shell), with its horizontal and vertical trim ε. Write e=t in the lower layer and e=2t−sign(t)/2 in the upper layer. Let the one-block energy be F(s,t)=φ(s)+(1+e)² for any measurable φ, and let σ be its standard deviation under normalized area measure on the trimmed block. Suppose all ordinary-primary torus progressions therein satisfy

    F(x)+F(z)−2F(y) ≥ λ(s_x−s_z)²,       λ ≥ 0.

There is an absolute c>0 for which σ ≥ c max(ε⁻²,λ) whenever 0<ε≤1/16384 (allowing infinite variance). Thus √λ/σ=O(ε) whenever the variance is finite. No regularity or convexity is assumed of φ in advance.

**An explicit progression.** In the notation of the original code put b=1/(2h)=3√2/4, p=b(1−R), u=s−1/2, I=[1/32,1/16]. In the relevant upper band the positive and negative lower edges are ℓ₊(u)=pu and ℓ₋(u)=−1/2+pu+b(G−u). The negative upper edge is h₋(u)=−ℓ(u)−b(V−u)/2. They obey ℓ₊+ℓ₋=2h₋ since 2R=G+V+1/(2b) (substitute R=2(1+h)/7, G=R/2, V=(3−4h)/7). The public README of #163553 omitted the divisor 2 in its displayed v. Its checker and construction both use v=b(V−u)₊/2, which is the formula used here.

For every u∈I and d=8ε/b, take endpoints with horizontal coordinates u−d,u+d and physical vertical coordinates

    t_x=ℓ₊(u−d)+2ε,    t_z=ℓ₋(u+d)+2ε.

Their ordinary midpoint has t_y=h₋(u)−2ε. All three lie strictly inside the trimmed fibres. Indeed the horizontal coordinates lie in (1/64,5/64) inside the first affine band, the two fibre widths there exceed 1/8, and the margins are 2ε. The accompanying verifier checks the inclusions exactly at the four corners of I×[0,1/16384]. Affinity extends them to the entire rectangle. At ε>0 the prescribed edge margins strictly exceed ε.

Set a=e_x, b₁=e_y, c=e_z. These lie in [−1/2,1/2] and a+c=2b₁−1, so b₁≥0. Therefore

    (1+a)²+(1+c)²−2(1+b₁)² = (a−c)²/2−2b₁−3/2 ≤ −1.

The theorem's assumption now gives the discrete curvature inequality Φ(u−d)+Φ(u+d)−2Φ(u)≥1 on I, where Φ(u)=φ(1/2+u).

**From local curvature to variance.** Let L=|I|, let J be the concentric interval of length L/2 and put h₀=L/4. For k=floor(h₀/d)≥h₀/(2d), add the last inequality at u+jd with weights k−|j|, for −k<j<k. For every u in J this gives Φ(u−kd)+Φ(u+kd)−2Φ(u)≥k². The weights sum to k², and all other coefficients cancel. The checked Lean lemma proves this for arbitrary finite stencils.

For all t∈T=[1/8,1/4] the points (1/2+u,t), u∈I, lie in the positive lobe. The same second difference of F at horizontal step kd is therefore ≥k² on J×T. At horizontal step h₀ all three points also form an ordinary torus progression with the same t, so the corresponding difference of F is ≥4λh₀² on the same rectangle.

For either step H, write D_H F for the second difference. Each of the three translates of J×T lies in the block, and the L² triangle inequality after subtracting the mean gives

    ||D_H F||₂ on J×T ≤ 4 ||F−mean(F)||₂ on the block ≤ 4σ.

These norms use unnormalized area. The last inequality uses area ≤1. Hence σ ≥ sqrt(|J||T|) max(k²,4λh₀²)/4. Since d=8ε/b this proves the theorem. If an energy has no finite second moment, the second-moment bin estimate is unavailable.

**Implication for the logarithm.** In the existing ellipsoid/one-shell/Chebyshev estimate, with the coefficient of the doubled secondary metric fixed, the available bin width is a constant times m√λ N^(−1/m). The central band has length a constant times σ√m. The ratio of these two quantities is at most C√m ε N^(−1/m), regardless of φ. The uniform trim removes at least c₁ε area (for instance the single lower interval over a fixed interior horizontal interval loses 2ε per fibre). Thus, even allowing the trim to vary, the factor multiplying A^m N^(−1/m) in this particular volume-and-variance estimate is at most C√m ε exp(−c₂mε)=O(m^(−1/2)). At the usual m of order √log N, this is the existing (log N)^(−1/4) power. This conclusion concerns the numerical lower bound certified by that argument; the actual heaviest window could be larger.

**Reproduction.** Run `python3 verify_barrier.py /path/to/erdos142-deterministic-shell` with the two Python verifiers from the linked commit in that directory. Lean 4.33.1 and the matching Mathlib compile `FibreBarrier.lean`, which proves the signed secondary loss and the discrete second-difference amplification. The variance estimate and its application are written proofs for review. The asymptotic equivalent in Erdős #142 remains open in this work.
