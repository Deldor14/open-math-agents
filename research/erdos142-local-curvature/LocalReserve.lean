import Mathlib

namespace LocalReserve

/-- A symmetric second difference of a convex function increases with radius. -/
theorem symmetric_comparison (f : ℝ → ℝ) (hc : ConvexOn ℝ Set.univ f)
    (y d r : ℝ) (hr : 0 ≤ r) (hrd : r ≤ d) :
    f (y-r) + f (y+r) ≤ f (y-d) + f (y+d) := by
  by_cases hd : d = 0
  · have : r = 0 := by linarith
    simp [hd, this]
  have hd' : 0 < d := by rcases lt_or_gt_of_ne hd with h | h <;> linarith
  let a := (d+r)/(2*d)
  let b := (d-r)/(2*d)
  have ha : 0 ≤ a := div_nonneg (by linarith) (by positivity)
  have hb : 0 ≤ b := div_nonneg (by linarith) (by positivity)
  have hab : a+b=1 := by dsimp [a,b]; field_simp; ring
  have left : a*(y-d)+b*(y+d)=y-r := by dsimp [a,b]; field_simp; ring
  have right : b*(y-d)+a*(y+d)=y+r := by dsimp [a,b]; field_simp; ring
  have h1 := hc.2 (Set.mem_univ (y-d)) (Set.mem_univ (y+d)) ha hb hab
  have h2 := hc.2 (Set.mem_univ (y-d)) (Set.mem_univ (y+d)) hb ha (by linarith : b+a=1)
  simp only [smul_eq_mul,left,right] at h1 h2
  calc
    _ ≤ (a*f (y-d)+b*f (y+d))+(b*f (y-d)+a*f (y+d)) := add_le_add h1 h2
    _ = _ := by linear_combination (f (y-d)+f (y+d))*hab

/-- A denominator bounded below by one half gives the required crossing budget. -/
theorem crossing (v D gain : ℝ) (hD : 1/2 ≤ D) (hg : 4*v^2 ≤ gain) :
    2*v^2/D ≤ gain := by
  apply (div_le_iff₀ (by linarith : 0 < D)).2
  have hnon : 0 ≤ gain := by nlinarith [sq_nonneg v]
  nlinarith [mul_nonneg hnon (show 0 ≤ D-1/2 by linarith)]

/-- The midpoint hinge covers the peak of an angular perspective tent. -/
theorem peak (y av len D : ℝ) (hD : 1/2 ≤ D) (h : av ≤ y)
    (hsize : y+av ≤ len) (hl : 0 ≤ len) :
    2*(y^2-av^2)/D ≤ 4*len*(y-av) := by
  apply (div_le_iff₀ (by linarith : 0 < D)).2
  have hx : 0 ≤ y-av := by linarith
  have hz : 0 ≤ 4*len*(y-av) := by positivity
  nlinarith [mul_nonneg hx (sub_nonneg.mpr hsize),
             mul_nonneg hz (show 0 ≤ D-1/2 by linarith)]

#print axioms symmetric_comparison
#print axioms crossing
#print axioms peak
end LocalReserve
