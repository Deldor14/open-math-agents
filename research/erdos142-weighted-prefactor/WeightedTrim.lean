import Mathlib.Tactic

namespace AsymmetricWeightedShell

/-- The seam hinge pays the smaller of the two endpoint depths. -/
theorem seam_hinge {l r : ℝ} (hl : 0 ≤ l) (hr : 0 ≤ r) :
    max 0 (-l) + max 0 r - 2 * max 0 ((r-l)/2) = min l r := by
  rcases le_total l r with h | h
  · rw [max_eq_left (by linarith : -l ≤ 0), max_eq_right hr,
        max_eq_right (by linarith : 0 ≤ (r-l)/2), min_eq_left h]
    ring
  · rw [max_eq_left (by linarith : -l ≤ 0), max_eq_right hr,
        max_eq_left (by linarith : (r-l)/2 ≤ 0), min_eq_right h]
    ring

/-- Removing the top deficiency pays the displacement of the negative endpoint. -/
theorem angular_gap {b r t x : ℝ} (hb : 0 < b) (hx : x < r/2) :
    1/2-t+b*x-max 0 (b*r/2-t) < 1/2 := by
  have h := le_max_right (0:ℝ) (b*r/2-t)
  nlinarith [mul_pos hb (sub_pos.mpr hx)]

/-- Bootstrap bound for the combined energy on an ordinary-primary AP. -/
theorem ordinary_metric {K d q f p : ℝ}
    (hf : K*d^2/4+q^2/8 ≤ f) (hp : -d^2/2 ≤ p) (hK : 0 ≤ K) :
    K*d^2/2+q^2/2 ≤ 4*f+K*p := by
  nlinarith [mul_nonneg hK (by linarith : 0 ≤ p+d^2/2)]

/-- The rank-one angular perspective contributes its cross term to the determinant. -/
theorem metric_det {A K b c r : ℝ} :
    (A*K + r*b^2)*(A + r*c^2) - (r*b*c)^2
      = A^2*K + A*r*b^2 + A*K*r*c^2 := by ring

/-- Exact change of ratios used before the uniform small-displacement approximation. -/
theorem ratio_difference {a₁ a₂ d₁ d₂ : ℝ}
    (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) :
    a₁/d₁-a₂/d₂ =
      ((a₁-a₂)+(a₁/d₁)*(d₂-d₁))/d₂ := by
  field_simp
  ring

end AsymmetricWeightedShell
