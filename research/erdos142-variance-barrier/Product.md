# Unequal trims and coupled energies on a product

Deldor14, 28 November 2026. This is a corollary of the [four-endpoint envelope theorem](https://github.com/Deldor14/open-math-agents/blob/8d29fee57b022a5880e570d6d937116e04d90ce2/research/erdos142-variance-barrier/Envelope.md).

Let block i be a copy of the oriented polygon with uniform trim εᵢ∈(0,1/65536]. Equip the Cartesian product of m such blocks with the product of their normalized area measures. Let F be any bounded Borel energy on the product. It may couple all 2m coordinates. Suppose its midpoint defect dominates

    Σᵢ [λᵢ(s_xᵢ−s_zᵢ)² + βᵢ ||2(t_xᵢ−t_zᵢ)||²]

on progressions whose primary midpoints are ordinary in all coordinates. Assume λᵢ,βᵢ>0. Then

    sd(F)² ≥ c Σᵢ max(λᵢ², βᵢ² εᵢ⁻⁴)

for an absolute c. Boundedness here avoids qualifications about sections on null rows.

**Proof.** Subtract the mean of F. Define fᵢ(z) by integrating F over all coordinates except i, using normalized block measures. Fix a progression in block i and hold all other blocks identical in its three points. Integrating its defect shows that fᵢ/βᵢ satisfies the one-block theorem with primary coefficient λᵢ/βᵢ. Thus sd(fᵢ)≥c₀ max(λᵢ,βᵢ εᵢ⁻²). The functions fᵢ of independent blocks are mean zero and pairwise orthogonal in L², and ⟨F,fᵢ⟩=||fᵢ||₂². Expanding the nonnegative squared norm of F−Σᵢ fᵢ gives the claim.

**Consequence for this extraction.** The 2m-dimensional ellipsoid used in the existing volume argument has denominator (Πᵢ λᵢ βᵢ)^(1/2) in its volume, so the standard union-bound choice of squared radius, hence the shell width up to a fixed factor, scales as m(Πᵢ λᵢ βᵢ)^(1/(2m)) N^(−1/m). Each √(λᵢβᵢ) is at most εᵢ max(λᵢ,βᵢ εᵢ⁻²). The arithmetic–geometric mean inequality and the variance bound yield

    m (Πᵢ λᵢ βᵢ)^(1/(2m)) / sd(F) ≤ C √m (Πᵢ εᵢ)^(1/m).

The volume of each trimmed block is at most A exp(−c₁ εᵢ) with c₁>0 absolute, by the area loss on a fixed lower-layer interval. Put t=Σᵢ εᵢ. The trim factor times the last bound is at most C√m·(t/m) exp(−c₁t)=O(m^(−1/2)). In the volume/variance proof the resulting factor multiplying N A^m N^(−1/m) therefore remains at most a constant times m^(−1/2), even when the energy couples the blocks, their metric weights differ, and their trims are optimized separately. This calculation does not bound the actual occupancy of energy windows and does not address nonproduct sampling domains.

**Cross terms for componentwise representatives.** The same conclusion holds for a positive-definite real matrix Q on the chosen difference representatives if an endpoint pair differing only in block i has vector supported in that block, with coordinates (ordinary primary difference, signed representative of the doubled secondary difference of least absolute value). The argument also works with circular primary representatives on the short horizontal test steps. Write the principal 2×2 matrix Qᵢ with diagonal entries aᵢ,bᵢ and off-diagonal entry cᵢ. On a one-block slice the quadratic form is ≥(det(Qᵢ)/aᵢ) times the square of the secondary representative, by completing the square. On the horizontal test rectangle it equals aᵢ times the squared primary difference. The same two tests therefore give sd(fᵢ)≥c₀ max(aᵢ, det(Qᵢ)/(aᵢ εᵢ²)). Hadamard–Fischer gives det(Q)≤Πᵢ det(Qᵢ), also obtained by successively taking positive Schur complements. Hence the same arithmetic–geometric mean calculation bounds m det(Q)^(1/(2m))/sd(F). This extension is for the usual ellipsoid-volume estimate and the stated representatives. A full lattice minimization over coupled lifts need not restrict to the principal form on a one-block slice.
