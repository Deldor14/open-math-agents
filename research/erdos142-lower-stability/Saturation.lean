import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open MeasureTheory Set

namespace Erdos142Saturation

/-- The cost of the lower partner R-s/2 is counted twice, and the cost of
the upper middle R/2+s/4 four times, with no pointwise regularity required. -/
theorem paired_rows {R : ℝ} (hR : 0≤R) {d l u : ℝ→ℝ}
    (hd : IntervalIntegrable d volume 0 R)
    (hl : IntervalIntegrable (fun s => l (R-s/2)) volume 0 R)
    (hu : IntervalIntegrable (fun s => u (s/4+R/2)) volume 0 R)
    (hpair : d ≤ᵐ[volume.restrict (Icc 0 R)] fun s => l (R-s/2)+u (s/4+R/2)) :
    (∫ s in 0..R, d s) ≤ 2*(∫ s in R/2..R, l s) + 4*(∫ s in R/2..3*R/4, u s) := by
  have hi := intervalIntegral.integral_mono_ae_restrict hR hd (hl.add hu) hpair
  rw [intervalIntegral.integral_add hl hu,
    intervalIntegral.integral_comp_sub_div l (by norm_num : (2:ℝ)≠0),
    intervalIntegral.integral_comp_div_add u (by norm_num : (4:ℝ)≠0)] at hi
  simpa only [zero_div,sub_zero,zero_add,smul_eq_mul,
    show R-R/2=R/2 by ring, show R/4+R/2=3*R/4 by ring] using hi

/-- Combine the earlier four band weights with the reverse transfer. Split
the last band at R/2 and R; only its middle piece is charged for a partner. -/
theorem combine {S A net a b c front tail last U u : ℝ}
    (hb : S-A ≤ net+3*a+4*b+2*(front+tail+last))
    (hr : net≤2*tail+4*u) (hu : u≤U)
    (ha : 0≤a) (hc : 0≤c) (hf : 0≤front) (hz : 0≤last) :
    S-A≤4*(a+b+c+front+tail+last+U) := by linarith

end Erdos142Saturation
#print axioms Erdos142Saturation.paired_rows
#print axioms Erdos142Saturation.combine
