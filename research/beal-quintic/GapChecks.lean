import Mathlib
open scoped BigOperators

namespace QuinticGap

private lemma power_sub_one (z : ℂ) (hz : ‖z‖ = 1) (k : ℕ) :
    ‖z^k - 1‖ ≤ k * ‖z - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      ‖z^(k+1) - 1‖ = ‖(z^k-1)*z + (z-1)‖ := by congr 1; ring
      _ ≤ ‖(z^k-1)*z‖ + ‖z-1‖ := norm_add_le _ _
      _ ≤ ((k+1:ℕ):ℝ) * ‖z-1‖ := by rw [norm_mul, hz]; push_cast; linarith

theorem geom_sum_lower (p : ℕ) (hp : 1 ≤ p) (z : ℂ) (hz : ‖z‖=1)
    (hsmall : ((p:ℝ)-1)*‖z-1‖ ≤ 1) :
    (p:ℝ)/2 ≤ ‖∑ i ∈ Finset.range p, z^i‖ := by
  have sum_indices (n : ℕ) :
      2 * (∑ i ∈ Finset.range n, (i:ℝ)) = (n:ℝ) * (n-1:ℝ) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ]; push_cast; linarith
  have h₁ : ‖(∑ i ∈ Finset.range p, z^i) - (p:ℂ)‖ ≤ (p:ℝ)/2 := by
    calc
      _ = ‖∑ i ∈ Finset.range p, (z^i-1)‖ := by simp [Finset.sum_sub_distrib]
      _ ≤ ∑ i ∈ Finset.range p, ‖z^i-1‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range p, ((i:ℝ)*‖z-1‖) :=
        Finset.sum_le_sum fun i _ => power_sub_one z hz i
      _ = (∑ i ∈ Finset.range p, (i:ℝ)) * ‖z-1‖ := (Finset.sum_mul ..).symm
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ (p:ℝ) by positivity)
        nlinarith [congrArg (fun t : ℝ => t*‖z-1‖) (sum_indices p)]
  have h₂ := norm_add_le ((p:ℂ) - ∑ i ∈ Finset.range p, z^i) (∑ i ∈ Finset.range p, z^i)
  rw [sub_add_cancel, norm_sub_rev] at h₂
  have h₃ : ‖(p:ℂ)‖ = (p:ℝ) := by simp
  rw [h₃] at h₂
  linarith

theorem centered_identity (a b : ℚ) :
    16*(a^4-a^3*b+a^2*b^2-a*b^3+b^4) =
    (a+b)^4+10*(a-b)^2*(a+b)^2+5*(a-b)^4 := by ring

#print axioms geom_sum_lower
#print axioms centered_identity
end QuinticGap
