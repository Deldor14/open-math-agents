import Mathlib.Tactic

namespace EnergiaOrientata

noncomputable def F (K s e : ℝ) := K*s^2 + (e+1)^2

/-- Local energy defect for a trimmed oriented block. The close ordinary
midpoint assumption is the equal-fibre chart inequality after trimming.
d is the projected circle distance of the secondary endpoints. -/
theorem difetto {K ε sx sy sz a b c d : ℝ}
    (hK : 32 ≤ K) (hε : 0 < ε) (hscale : 32 ≤ K*ε^2)
    (hsy : 0 ≤ sy) (hb : -(1/2:ℝ) ≤ b ∧ b ≤ 1/2)
    (hd : 0 ≤ d ∧ d ≤ 1/2)
    (hcarry : sx+sz=2*sy ∨ sx+sz=2*sy+1)
    (hclose : sx+sz=2*sy → |sx-sz|<ε →
      2*b ≤ a+c ∧ d ≤ 2*|a-c|) :
    K*(sx-sz)^2/4+d^2/8 ≤ F K sx a+F K sz c-2*F K sy b := by
  have hK0 : 0 ≤ K := by linarith
  have hks := mul_nonneg hK0 (sq_nonneg (sx-sz))
  have hb1 : (b+1)^2 ≤ (3/2:ℝ)^2 := by
    apply sq_le_sq' <;> linarith [hb.1,hb.2]
  have hd1 : d^2 ≤ (1/2:ℝ)^2 := by
    apply sq_le_sq' <;> linarith [hd.1,hd.2]
  unfold F
  rcases hcarry with hz | hz
  · have h0 : sx^2+sz^2-2*sy^2=(sx-sz)^2/2 := by
      linear_combination (sx+sz+2*sy)*hz/2
    have hzK := congrArg (K*·) h0
    by_cases hh : |sx-sz| < ε
    · obtain ⟨hmid, hdist⟩ := hclose hz hh
      have hsq : d^2 ≤ (2*|a-c|)^2 := by
        apply sq_le_sq' <;> linarith [abs_nonneg (a-c),hd.1]
      simp only [mul_pow,sq_abs] at hsq
      have hconv : 0 ≤ (a+c-2*b)*(a+c+2*b+4) := by
        apply mul_nonneg <;> linarith [hb.1]
      nlinarith
    · have hε2 : ε^2 ≤ (sx-sz)^2 := by
        rw [← sq_abs (sx-sz)]
        apply sq_le_sq' <;> linarith [abs_nonneg (sx-sz),not_lt.mp hh]
      have hfar := mul_le_mul_of_nonneg_left hε2 hK0
      nlinarith [sq_nonneg (a+1),sq_nonneg (c+1)]
  · have h1 : sx^2+sz^2-2*sy^2=(sx-sz)^2/2+2*sy+1/2 := by
      linear_combination (sx+sz+2*sy+1)*hz/2
    have hzK := congrArg (K*·) h1
    nlinarith [sq_nonneg (a+1),sq_nonneg (c+1),mul_nonneg hK0 hsy]

end EnergiaOrientata
