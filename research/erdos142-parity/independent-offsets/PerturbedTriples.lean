import Mathlib

namespace Erdos142Perturbation

/-- On a nonzero displacement t, a collision of three corrected images with
three distinct original sites would use the three different shift labels.
Their original defect would then be zero or ±3t. -/
theorem corrected_endpoints_distinct
    (x y z t i j k : ℤ) (ht : 0 < t)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hi : 0 ≤ i) (hi' : i ≤ 2) (hj : 0 ≤ j) (hj' : j ≤ 2)
    (hk : 0 ≤ k) (hk' : k ≤ 2)
    (hdef : x+z-2*y = t ∨ x+z-2*y = -t ∨
      x+z-2*y = 2*t ∨ x+z-2*y = -(2*t) ∨
      x+z-2*y = 4*t ∨ x+z-2*y = -(4*t))
    (hmid : x+i*t + (z+k*t) = 2*(y+j*t)) :
    x+i*t ≠ z+k*t := by
  intro h
  interval_cases i <;> interval_cases j <;> interval_cases k <;>
    norm_num at * <;> omega

/-! For a symmetric jitter law, let p be the probability of either
extreme offset and 1−2p the probability of the central offset.
The smaller of the probabilities for defects t and 4t is maximised
at the crossing in the interval [1/3,1/2]. -/
theorem odd_probability_decreases {p q : ℝ} (hp : 1/3 ≤ p) (hpq : p ≤ q)
    (hq : q ≤ 1/2) :
    2*q*(1-2*q)*(1-q) ≤ 2*p*(1-2*p)*(1-p) := by
  have h₁ : 1-2*q ≤ 1-2*p := by linarith
  have h₂ : q*(1-2*q) ≤ p*(1-2*p) := by
    nlinarith [mul_nonneg (show 0 ≤ q-p by linarith)
      (show 0 ≤ 2*(p+q)-1 by linarith)]
  nlinarith [mul_nonneg (show 0 ≤ 1-q by linarith)
      (sub_nonneg.mpr h₂), mul_nonneg (mul_nonneg (show 0 ≤ p by linarith)
      (show 0 ≤ 1-2*p by linarith)) (sub_nonneg.mpr hpq)]

#print axioms corrected_endpoints_distinct
#print axioms odd_probability_decreases
end Erdos142Perturbation
