import Mathlib.Tactic

namespace Erdos142Review

/-- Finite lower comparison at a fixed input scale. Here u = √d, D is
the seed deficit and b is the number of low-information cuts. -/
theorem few_low_cuts (η u t D b : ℝ) (hη : 0 < η) (hu : 0 < u)
    (ht : 0 ≤ t) (hD : 0 < D) (hcap : D ≤ 5*u)
    (hscale : 128*t ≤ η*D*u) (hcount : b*D ≤ 2*t*(10*u+D)) :
    b < η*u^2/2 := by
  have h₁ : 2*t*(10*u+D) ≤ 30*t*u := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hcap)]
  have h₂ := mul_le_mul_of_nonneg_right hscale hu.le
  have h₃ : 0 < η*D*u^2 := by positivity
  by_contra! hf
  have hh := mul_le_mul_of_nonneg_right hf hD.le
  nlinarith

/-- In the guarded product, the extra incomplete digit costs at most g.
Here g is D_t + log 2. -/
theorem guarded_budget (u t g : ℝ) (hu : 0≤u) (ht : 0<t)
    (hgcap : g≤5*u) (hscale : u*g≤t) :
    (u^2/t+1)*g ≤ 6*u := by
  have hh := mul_le_mul_of_nonneg_left hscale hu
  have hh' : u^2*g/t ≤ u := (div_le_iff₀ ht).2 (by nlinarith)
  have heq : (u^2/t+1)*g = u^2*g/t+g := by ring
  linarith [heq]

end Erdos142Review

#print axioms Erdos142Review.few_low_cuts
#print axioms Erdos142Review.guarded_budget
