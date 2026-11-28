import Mathlib

namespace ConcaveDual

noncomputable def circleArea : ℝ := (17 - 6 * Real.sqrt 2) / 28
noncomputable def parameter : ℝ := 4 * circleArea - 1
noncomputable def optimalLength : ℝ := 2 * (1 + Real.sqrt 2 / 3) / 7
noncomputable def g (L : ℝ) : ℝ := (parameter + 16*L - 4)/14
noncomputable def j (L : ℝ) : ℝ := g L - parameter/2
noncomputable def w (L : ℝ) : ℝ := g L/2 + parameter/4
noncomputable def reflect (L : ℝ) : ℝ := 2*L - 1/2
noncomputable def moment (L a b : ℝ) : ℝ := (b-a)*(L-(a+b)/2)

theorem constant_part (L : ℝ) :
    w L/2-j L/4 = circleArea-1/4 := by
  unfold w j g parameter; ring

theorem right_moment (L : ℝ) :
    moment L 0 (j L)/2 + moment L (j L) (w L) - moment L (g L) L
      - moment L (reflect L-j L) (reflect L) = 9/14*(L-optimalLength)^2 := by
  unfold moment j w g reflect parameter optimalLength circleArea
  have h : Real.sqrt 2^2 = 2 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [h]
  ring

theorem left_moment (L : ℝ) :
    moment L 0 (w L) - moment L (w L) L
      - moment L (reflect L-j L) (reflect L)/2
      - moment L (reflect L-g L) (reflect L-w L) = 9/14*(L-optimalLength)^2 := by
  unfold moment j w g reflect parameter optimalLength circleArea
  have h : Real.sqrt 2^2 = 2 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [h]
  ring

theorem short_chord_balance (L : ℝ) :
    let m := L*(1-Real.sqrt 2/2)
    moment L 0 m = moment L m L := by
  dsimp [moment]
  have h : Real.sqrt 2^2 = 2 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [h]
  ring

theorem chord_dominates {k actual chord : ℝ}
    (h : (k ≤ 0 ∧ chord ≤ actual) ∨ (0 ≤ k ∧ actual ≤ chord)) :
    k*actual ≤ k*chord := by
  rcases h with ⟨hs, hv⟩ | ⟨hs, hv⟩
  · exact mul_le_mul_of_nonpos_left hv hs
  · exact mul_le_mul_of_nonneg_left hv hs

end ConcaveDual
#print axioms ConcaveDual.right_moment
#print axioms ConcaveDual.left_moment
#print axioms ConcaveDual.constant_part
#print axioms ConcaveDual.short_chord_balance
#print axioms ConcaveDual.chord_dominates
