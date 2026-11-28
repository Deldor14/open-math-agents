import Mathlib.Tactic

namespace Erd142FlatBand

/-- Convex endpoint bounds and the two boundary midpoint inequalities
force all values appearing in the two witnesses to agree. -/
theorem endpoint_equal {A B D X Z r p q : ℝ}
    (hr' : r < 1)
    (hp : 0 < p) (hq : 0 < q)
    (hB : B ≤ (1-r)*A+r*D)
    (hX : X ≤ (1-p)*A+p*D) (hZ : Z ≤ (1-q)*A+q*D)
    (hUp : 2*D ≤ A+B) (hDown : 2*A ≤ X+Z) :
    A = D ∧ B = A := by
  have hDA : D ≤ A := by
    by_contra! h
    nlinarith [mul_pos (by linarith : 0 < 1-r) (sub_pos.mpr h)]
  have hAD : A ≤ D := by
    by_contra! h
    nlinarith [mul_pos hp (sub_pos.mpr h),mul_pos hq (sub_pos.mpr h)]
  have he := le_antisymm hAD hDA
  subst D
  constructor
  · rfl
  · nlinarith

/-- The incoming angular midpoint on the negative sheet. -/
theorem shifted_upper {a b d t k : ℝ} (hd : d=(a+b)/2+1/2) :
    ((a-t+k/2)+(b+t-2*k+k/2))/2+1/2=d-k/2 := by
  linarith

/-- Deficit in a lower endpoint forces a second difference of the maxima. -/
theorem difference_dominates {left middle right endpoint other loss : ℝ}
    (hl : loss ≤ left-endpoint) (hr : other ≤ right)
    (hm : 2*middle ≤ endpoint+other) :
    loss ≤ left+right-2*middle := by
  linarith

end Erd142FlatBand
