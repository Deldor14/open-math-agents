import Mathlib.Tactic

namespace ShellMass

/-- Three values confined to an interval of length L have defect at most 2L. -/
theorem quantile_span {x y z a L loss : ℝ} (hx : x ≤ a+L) (hz : z ≤ a+L)
    (hy : a ≤ y) (h : loss ≤ x+z-2*y) : loss ≤ 2*L := by linarith

/-- A uniform lower slope for the excess above r² bounds radial shell area. -/
theorem radial {f₁ f₂ r₁ r₂ W : ℝ}
    (h : f₁-r₁^2 ≤ f₂-r₂^2) (hw : f₂-f₁ ≤ W) :
    r₂^2-r₁^2 ≤ W := by linarith

/-- Matrix shear cannot increase the secondary lower coefficient in this test. -/
theorem schur_slice {a b c s t : ℝ} (ha : 0<a) :
    ((a*b-c^2)/a)*t^2 ≤ a*s^2 + 2*c*s*t + b*t^2 := by
  field_simp [ha.ne']
  nlinarith [sq_nonneg (a*s+c*t)]

/-- The geometric mean of two competing scale factors never exceeds their maximum. -/
theorem scales {p q e h : ℝ} (hh : 0 ≤ h)
    (hp : 0 ≤ p) (hp' : p ≤ h) (hq : q ≤ h*e^2) :
    p*q ≤ (e*h)^2 := by
  calc
    p*q ≤ p*(h*e^2) := mul_le_mul_of_nonneg_left hq hp
    _ ≤ h*(h*e^2) := mul_le_mul_of_nonneg_right hp' (mul_nonneg hh (sq_nonneg e))
    _ = _ := by ring

end ShellMass
