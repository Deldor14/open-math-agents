import Mathlib.Tactic

namespace Erdos142Deterministic

/-- The conditional second-moment objective after one uniformly chosen block. -/
theorem conditional_mean {ι : Type*} (s : Finset ι) (f : ι → ℝ) (c L r v : ℝ)
    (hmean : ∑ x ∈ s, f x = 0) (hvar : ∑ x ∈ s, (f x)^2 = (s.card : ℝ)*v) :
    ∑ x ∈ s, (L-(c+f x)^2-r*v) = (s.card : ℝ)*(L-c^2-(r+1)*v) := by
  calc
    _ = ∑ x ∈ s, ((L-c^2-r*v)-(2*c)*f x-(f x)^2) := by
      apply Finset.sum_congr rfl
      intros
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hmean, hvar,
        Finset.sum_const, nsmul_eq_mul, mul_zero, sub_zero]
      ring

/-- Positive metric separation prevents three energies sharing a sufficiently narrow window. -/
theorem separated_window {ι : Type*} (s : Finset ι) (dist x y z : ι → ℝ)
    (w a : ℝ) (sep : 16*w ≤ ∑ i ∈ s, dist i)
    (localBound : ∀ i ∈ s, dist i ≤ 8*(x i+z i-2*y i))
    (hx : (∑ i ∈ s, x i) < a+w) (hz : (∑ i ∈ s, z i) < a+w)
    (hy : a ≤ ∑ i ∈ s, y i) : False := by
  have h := Finset.sum_le_sum localBound
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib] at h
  linarith

#print axioms conditional_mean
#print axioms separated_window
end Erdos142Deterministic
