import Mathlib

namespace BohrGrid

/-- Weak duality with coordinate width caps filling the residual demand. -/
theorem width_dual {ι κ : Type*} [Fintype ι] [Fintype κ]
    (width cap : ι → ℝ) (a : κ → ι → ℝ) (p : κ → ℝ) (r : ι → ℝ)
    (hw : ∀ i, 0 ≤ width i) (hc : ∀ i, width i ≤ cap i)
    (hp : ∀ k, 0 ≤ p k) (hr : ∀ i, 0 ≤ r i)
    (row : ∀ k, ∑ i, a k i * width i ≤ 1)
    (load : ∀ i, 1 ≤ (∑ k, p k * a k i) + r i) :
    ∑ i, width i ≤ (∑ k, p k) + ∑ i, r i * cap i := by
  classical
  calc
    ∑ i, width i ≤ ∑ i, ((∑ k, p k * a k i) + r i) * width i := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (load i) (hw i)
    _ = (∑ k, p k * ∑ i, a k i * width i) + ∑ i, r i * width i := by
      simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul,
        Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun i k => p k * (a k i * width i))]
    _ ≤ _ := by
      apply add_le_add <;> apply Finset.sum_le_sum
      · intro k _
        simpa using mul_le_mul_of_nonneg_left (row k) (hp k)
      · intro i _
        exact mul_le_mul_of_nonneg_left (hc i) (hr i)

theorem paired_threshold {x y : ℝ} (hx : x ≤ 143/480) (hy : y ≤ 29/96) :
    (x+y)/2 ≤ 3/10 := by linarith

/-- Union-bound deduction for three centered triangular weights. -/
theorem hole_threshold {q mass loss : ℝ} (h : 0 < q)
    (peak : (q/2)^3 ≤ mass) (damaged : mass ≤ (q/2)*loss) :
    q^2 ≤ 4*loss := by
  by_contra! bad
  have hh := mul_lt_mul_of_pos_left bad h
  nlinarith

#print axioms width_dual
#print axioms paired_threshold
#print axioms hole_threshold
end BohrGrid
