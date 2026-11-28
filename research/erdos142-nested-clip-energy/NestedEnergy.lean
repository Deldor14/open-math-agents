import Mathlib

namespace NestedEnergy

/-- The slack in the child midpoint inequality survives inverse denominators. -/
theorem reciprocal_slack (a b d : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : a ≤ 2) (hB : b ≤ 2) (hd : 0 ≤ d) (hs : d ≤ 2*(b-a)) :
    d/4 ≤ 2*(1/a-1/b) := by
  have hp : 0 < a*b := mul_pos (by linarith) (by linarith)
  have hh := mul_nonneg (sub_nonneg.mpr hA) (show 0 ≤ b by linarith)
  have hab : a*b ≤ 4 := by nlinarith
  have hi : 2*(1/a-1/b) = 2*(b-a)/(a*b) := by
    field_simp [show a≠0 by linarith,show b≠0 by linarith]
  rw [hi]
  apply (le_div_iff₀ hp).2
  nlinarith [mul_nonneg hd (sub_nonneg.mpr hab)]

/-- The convex chord of the squared tent pays its peak exactly. -/
theorem peak_payment (w av len h D : ℝ) (hD : 1 ≤ D) (he : w-av=h)
    (hw : 0 ≤ h) (hl : 0 ≤ len) (hs : w+av ≤ len) :
    2*(w^2-av^2)/D ≤ 2*len*h := by
  apply (div_le_iff₀ (by linarith : 0<D)).2
  have h1 := mul_nonneg hw (sub_nonneg.mpr hs)
  have h2 := mul_nonneg (mul_nonneg hl hw) (sub_nonneg.mpr hD)
  rw [←he] at h1 h2 ⊢
  nlinarith

theorem ordinary_crossing (d w D : ℝ) (hw : 0 ≤ w) (h : w ≤ d) (hD : D ≤ 1) :
    (2*d)^2/4+w^2*D/20 ≤ (4/5:ℝ)*(2*d)^2/2-2*w^2/5 := by
  nlinarith [mul_nonneg (show 0 ≤ d-w by linarith) (show 0 ≤ d+w by linarith),
    mul_nonneg (sq_nonneg w) (sub_nonneg.mpr hD), sq_nonneg w]

theorem downward_crossing (d w D : ℝ) (hw : 0 ≤ w) (h : w ≤ 1/2) (hD : D ≤ 1) :
    d^2/4+w^2*D/20 ≤ (4/5:ℝ)*(d^2/2+1/2)-2*w^2/5 := by
  nlinarith [mul_nonneg (show 0 ≤ 1/2-w by linarith) (show 0 ≤ 1/2+w by linarith),
    mul_nonneg (sq_nonneg w) (sub_nonneg.mpr hD), sq_nonneg d]

theorem two_levels (a b u v : ℝ) :
    a^2/20*(b^2/16+u^2*v^2/480) =
        a^2*b^2/320+a^2*u^2*v^2/9600 := by ring

#print axioms reciprocal_slack
#print axioms peak_payment
#print axioms ordinary_crossing
#print axioms downward_crossing
#print axioms two_levels
end NestedEnergy
