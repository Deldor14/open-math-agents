import Mathlib

namespace EleventhRelative

/-- Two adjacent Farey fractions force an intervening denominator to be large. -/
theorem farey_separation (a b c d v q : ℤ) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hdet : b*c-a*d=1) (hl : a*q<b*v) (hr : d*v<c*q) : b+d≤q := by
  have h₁ : 1 ≤ b*v-a*q := by omega
  have h₂ : 1 ≤ c*q-d*v := by omega
  calc
    b+d ≤ b*(c*q-d*v)+d*(b*v-a*q) := by
      simpa only [mul_one] using add_le_add
        (mul_le_mul_of_nonneg_left h₂ hb) (mul_le_mul_of_nonneg_left h₁ hd)
    _ = q*(b*c-a*d) := by ring
    _ = q := by rw [hdet,mul_one]

/-- Transfer a two-logarithm estimate to a bound on the logarithm of D. -/
theorem log_separation (p L M B t : ℝ) (hL : 0<L) (ht : 0<t)
    (h : p < 126*M^2 + B/L) (hm : t*(126*M^2) ≤ (t-1)*p) :
    p*L < t*B := by
  have hs := (lt_div_iff₀ hL).mp (show p-126*M^2 < B/L by linarith)
  have hu := mul_lt_mul_of_pos_left hs ht
  have hv := mul_le_mul_of_nonneg_right hm hL.le
  nlinarith only [hu,hv]

end EleventhRelative

#print axioms EleventhRelative.farey_separation
#print axioms EleventhRelative.log_separation
