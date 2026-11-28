import Mathlib.Tactic

namespace CalibratedRothShell

/-- One active endpoint suffices when the other endpoint is inactive. -/
theorem single_active {x y dx dy : ℝ} (hy : 0 ≤ y) (hx : 2*y ≤ x)
    (hp : 0 < dx) (hq : 0 < dy) (h : dx ≤ 2*dy) :
    2*y^2/dy ≤ x^2/dx := by
  apply (div_le_div_iff₀ hq hp).2
  have hxx : 4*y^2 ≤ x^2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ x-2*y) (by linarith : 0 ≤ x+2*y)]
  nlinarith [mul_nonneg (sq_nonneg y) (by linarith : 0 ≤ 2*dy-dx),
             mul_nonneg hq.le (by linarith : 0 ≤ x^2-4*y^2)]

/-- The upward half-unit jump for the angular square calibrated at 1/4. -/
theorem upper_jump (v w : ℝ) :
    (v-1/4)^2+(w-1/4)^2-2*((v+w)/2+1/2-1/4)^2
      = (v-w)^2/2-(v+w) := by ring

/-- The downward half-unit jump costs twice the new angular coordinate. -/
theorem lower_jump (v w : ℝ) :
    (v-1/4)^2+(w-1/4)^2-2*((v+w)/2-1/2-1/4)^2
      = (v-w)^2/2+2*((v+w)/2-1/2) := by ring

/-- Lower bound at an incoming upper contact. -/
theorem contact {v w g b d : ℝ} (hg : 0 ≤ g) (hm : v+w ≤ 2*g)
    (hd : 2*g-2*b*d ≤ w-v) :
    -2*g*(1-g)-4*b*g*d ≤ (v-w)^2/2-(v+w) := by
  nlinarith [sq_nonneg ((w-v)-2*g),
             mul_nonneg hg (by linarith : 0 ≤ w-v-(2*g-2*b*d))]

/-- Active determinant, with primary curvature gamma and D=1-gv². -/
theorem active_det {a l gam g v D : ℝ} (h : D ≠ 0) (hD : D=1-g*v^2) :
    (gam+l/D)*(l*a^2*(4*g^2*v^2/D^3+g/D^2))-
      (l*a*2*g*v/D^2)^2
      = l*a^2*g*(l+gam+3*gam*g*v^2)/D^3 := by
  field_simp
  rw [hD]
  ring

end CalibratedRothShell
