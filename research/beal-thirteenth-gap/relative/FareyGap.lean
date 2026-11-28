import Mathlib

namespace BealRelativeGap

/-- Cross-multiplied form, with integral numerators and positive denominators. -/
theorem farey_denominator {a b c d m n : ℤ}
    (hb : 0 < b) (hd : 0 < d) (det : b*c-a*d=1)
    (left : a*n < b*m) (right : d*m < c*n) :
    b+d ≤ n := by
  have h₁ : 1 ≤ b*m-a*n := by omega
  have h₂ : 1 ≤ c*n-d*m := by omega
  calc b+d ≤ b*(c*n-d*m)+d*(b*m-a*n) := by
         nlinarith [mul_le_mul_of_nonneg_left h₁ hd.le,
                    mul_le_mul_of_nonneg_left h₂ hb.le]
       _ = (b*c-a*d)*n := by ring
       _ = n := by rw [det,one_mul]

end BealRelativeGap

#print axioms BealRelativeGap.farey_denominator
