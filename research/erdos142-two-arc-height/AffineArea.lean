import Mathlib

namespace AffineArea

/-- Exact loss in the central optimization chamber. -/
theorem chamber_squares (t b : ℝ) (ht : 0 < t) :
    (1/4 : ℝ) + (b/2 - b^2 - (1-2*t+b)^2/6)/(2*t)
      = (17-6*Real.sqrt 2)/28 - (4*Real.sqrt 2*t-3)^2/(112*t)
        - (7/(12*t))*(b-(4*t+1)/14)^2 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp [ne_of_gt ht]
  nlinarith only [hs, show (Real.sqrt 2)^2 * t^2 = 2*t^2 by rw [sq, hs]]

/-- Derivative multiplier in the t <= 1/2 reduction. -/
theorem increasing_margin {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) :
    0 ≤ b*(1-b) - (2*b+b^2)/6 := by
  have h : 0 ≤ b*(4-7*b) := mul_nonneg h0 (by linarith)
  linarith

/-- After subtracting the semicircle capacity z, the oriented trim is
the lower envelope of three explicit affine expressions. -/
theorem oriented_surplus (X Y z : ℝ) (hX : X ≤ z) :
    X+Y-z-(max 0 (2*X+Y-z-1/2) + max 0 (Y+z-1/2))/2 =
    min (X+Y-z) (min (1/4+X+Y/2-3*z/2) (1/2-z)) := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

end AffineArea
#print axioms AffineArea.chamber_squares
#print axioms AffineArea.increasing_margin
#print axioms AffineArea.oriented_surplus
