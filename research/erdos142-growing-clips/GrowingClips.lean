import Mathlib

namespace GrowingClips

/-- Primary coordinates scaled by 2k, so that 2u lies in upper bin h. -/
theorem earliest_sum (a b h : ℕ) (x z t : ℝ)
    (hx : a < x) (hz : b < z) (hs : x+z=t) (ht : t < (h:ℝ)+1) :
    a+b ≤ h := by
  by_contra! hn
  have hnat : h+1 ≤ a+b := by omega
  have hreal : (h:ℝ)+1 ≤ (a:ℝ)+b := by exact_mod_cast hnat
  linarith

/-- Mixed upper angular endpoints cannot jump up when the integer row test holds. -/
theorem no_half_jump (x z y l r top : ℝ) (hx : l<x) (hz : r<z)
    (hy : y<top) (check : 2*top≤l+r+1) :
    2*y≠x+z+1 := by linarith

/-- The positive gap at a downward ordinary-chart carry. -/
theorem downward_square (x y z : ℝ) (hy : 0≤y) (carry : x+z=2*y+1) :
    (x-z)^2/2+1/2 ≤ x^2+z^2-2*y^2 := by
  have he : x^2+z^2-2*y^2=(x-z)^2/2+2*y+1/2 := by
    have hz : z=2*y+1-x := by linarith
    rw [hz]; ring
  linarith

theorem volume :
    (2*98713058+75594412:ℚ)/(4*96*2048^2)=17063783/100663296 := by norm_num

theorem beats_planar :
    ((17-6*Real.sqrt 2)/28)^3 < (17063783/100663296:ℝ)^2 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hl : (1414:ℝ)/1000 ≤ Real.sqrt 2 := by nlinarith
  have hu : Real.sqrt 2 ≤ 2 := by nlinarith
  have h0 : 0 ≤ (17-6*Real.sqrt 2)/28 := by linarith
  have hh : (17-6*Real.sqrt 2)/28 ≤ (17-6*(1414/1000:ℝ))/28 := by linarith
  exact lt_of_le_of_lt (pow_le_pow_left₀ h0 hh 3) (by norm_num)

#print axioms earliest_sum
#print axioms no_half_jump
#print axioms downward_square
#print axioms volume
#print axioms beats_planar
end GrowingClips
