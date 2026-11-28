import Mathlib

namespace Erdos142Adaptive

private def weights : Fin 30 → ℕ := ![0,1,0,2,0,1,0,3,1,0,2,0,1,0,9,0,1,0,2,0,1,3,0,1,0,2,0,1,0,6]
private def positions : Fin 30 → ℕ := ![0,0,1,1,3,3,4,4,7,8,8,10,10,11,11,20,20,21,21,23,23,24,27,27,28,28,30,30,31,31]
private def weightSum (t : ℕ) : ℕ := 37*(t/30)+positions ⟨t%30,Nat.mod_lt _ (by decide)⟩

/-- The tabulated prefixes agree with the stated periodic letters, including wraparound. -/
theorem template_prefix : ∀ i : Fin 30, weightSum (i.val+1) = weightSum i.val + weights i := by
  decide +kernel

/-- All nonzero half-length residues have unequal adjacent sums modulo ten. -/
theorem template_avoidance : ∀ i j : Fin 30, j.val ≠ 0 →
    (weightSum (i.val+2*j.val) + weightSum i.val)%10 ≠ (2*weightSum (i.val+j.val))%10 := by
  decide +kernel

theorem affine_lift (n i j k x y z : ℤ) (hwidth : |x+z-2*y| < n)
    (heq : (n*i+x)+(n*k+z) = 2*(n*j+y)) : i+k=2*j := by
  have h : n*(i+k-2*j) = -(x+z-2*y) := by nlinarith only [heq]
  have hh := congrArg abs h
  rw [abs_mul, abs_neg, abs_of_pos (show 0<n by exact (abs_nonneg _).trans_lt hwidth)] at hh
  by_contra bad
  have hne : i+k-2*j ≠ 0 := by omega
  have : 1 ≤ |i+k-2*j| := Int.add_one_le_iff.mpr (abs_pos.mpr hne)
  have hn : 0 ≤ n := (abs_nonneg _).trans hwidth.le
  have hh2 := mul_le_mul_of_nonneg_left this hn
  rw [mul_one, hh] at hh2
  exact (not_lt_of_ge hh2) hwidth

#print axioms template_prefix
#print axioms template_avoidance
#print axioms affine_lift
end Erdos142Adaptive
