import Mathlib

namespace EndpointTents

/-- Negative semiconvexity of the squared tent paid by its center hinge. -/
theorem tent_payment (y av excess len D : ℝ) (hD : 1 ≤ D)
    (hy : 0 ≤ y) (ha : 0 ≤ av) (hlen : y+av ≤ len)
    (he : y-av = excess) (hpos : 0 ≤ excess) :
    2*(y^2-av^2)/D ≤ 2*len*excess := by
  have hp : 0 < D := by linarith
  apply (div_le_iff₀ hp).2
  have h1 : excess*(y+av) ≤ excess*len := mul_le_mul_of_nonneg_left hlen hpos
  have hlen0 : 0 ≤ len := by linarith
  have h2 := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 2*len*excess)
  nlinarith [show y^2-av^2 = excess*(y+av) by rw [←he]; ring]

theorem upward_square (x y z : ℝ) (carry : 2*y=x+z+1) (top : y ≤ 1/2) :
    -(3/2:ℝ) ≤ (x+1/2)^2+(z+1/2)^2-2*(y+1/2)^2 := by
  have h : (x+1/2)^2+(z+1/2)^2-2*(y+1/2)^2 =
      (x-z)^2/2 - 2*(y+1/2) + 1/2 := by
    have hy : y=(x+z+1)/2 := by linarith
    rw [hy]; ring
  rw [h]; nlinarith [sq_nonneg (x-z)]

theorem lower_carry (s D : ℝ) (hs : 0 ≤ s) (ht : s ≤ 1/2)
    (hD : 3/2-s ≤ D) : 2*(1/2-s)^2/D ≤ 1/3 := by
  have hp : 0 < D := by linarith
  apply (div_le_iff₀ hp).2
  nlinarith [mul_nonneg hs (show 0 ≤ 1/2-s by linarith)]

theorem contact_margin (H d : ℝ) (hd : 5/4 ≤ H*d) :
    1/16 ≤ H^2*d^2-3/2 := by
  nlinarith [mul_nonneg (show 0 ≤ H*d-5/4 by linarith)
    (show 0 ≤ H*d+5/4 by linarith),
    show (H*d-5/4)*(H*d+5/4) = H^2*d^2-25/16 by ring]

#print axioms tent_payment
#print axioms upward_square
#print axioms lower_carry
#print axioms contact_margin
end EndpointTents
