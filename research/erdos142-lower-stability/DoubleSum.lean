import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal

namespace Erdos142Lower

/-- Two translates of a set with its extreme elements attained overlap only
at their common endpoint. The container for the sumset can be any finite-
measure set, so no measurability assumption on the sumset is necessary. -/
theorem double_sum_inside {K Q : Set ℝ} {a b : ℝ} (hm : NullMeasurableSet K volume)
    (ha : a∈K) (hb : b∈K) (hbounds : K⊆Icc a b)
    (hQ : volume Q≠⊤) (hadd : ∀x∈K, ∀y∈K, x+y∈Q) :
    2*volume.real K ≤ volume.real Q := by
  let P := (fun x : ℝ => x-a) ⁻¹' K
  let N := (fun x : ℝ => x-b) ⁻¹' K
  have hmap (t : ℝ) := measurePreserving_sub_right (volume : Measure ℝ) t
  have hmN : NullMeasurableSet N volume := hm.preimage (hmap b).quasiMeasurePreserving
  have hP : volume.real P=volume.real K := by
    exact congrArg ENNReal.toReal ((hmap a).measure_preimage hm)
  have hN : volume.real N=volume.real K := by
    exact congrArg ENNReal.toReal ((hmap b).measure_preimage hm)
  have hPN : P∪N⊆Q := by
    rintro x (hx|hx)
    · simpa using hadd (x-a) hx a ha
    · simpa using hadd (x-b) hx b hb
  have hpt : P∩N⊆{a+b} := by
    intro x hx
    have h₁ := (hbounds hx.1).2
    have h₂ := (hbounds hx.2).1
    change x-a≤b at h₁
    change a≤x-b at h₂
    simp only [mem_singleton_iff]
    linarith
  have hz : volume.real (P∩N)=0 := by
    unfold Measure.real
    rw [measure_mono_null hpt (measure_singleton (a+b) : volume {a+b} = 0)]
    rfl
  have hfin : volume (P∪N)≠⊤ := measure_ne_top_of_subset hPN hQ
  have hunion := measureReal_union_add_inter₀ (s:=P) hmN
    (measure_ne_top_of_subset subset_union_left hfin) (measure_ne_top_of_subset subset_union_right hfin)
  have hmono := measureReal_mono hPN hQ
  linarith

/-- A surplus in one interval and the signed surplus in its translated
target can be charged together, including an almost-everywhere error. -/
theorem integrate_charge {a b d : ℝ} (hab : a≤b) {s t h : ℝ→ℝ}
    (hs : IntervalIntegrable s volume a b)
    (ht : IntervalIntegrable (fun x => t (x+d)) volume a b)
    (hh : IntervalIntegrable h volume a b)
    (hp : (fun x => s x+t (x+d)) ≤ᵐ[volume.restrict (Icc a b)] h) :
    (∫ x in a..b, s x) + (∫ y in a+d..b+d, t y) ≤ ∫ x in a..b, h x := by
  have hi := intervalIntegral.integral_mono_ae_restrict hab (hs.add ht) hh hp
  rw [intervalIntegral.integral_add hs ht, intervalIntegral.integral_comp_add_right] at hi
  exact hi

end Erdos142Lower
#print axioms Erdos142Lower.double_sum_inside
#print axioms Erdos142Lower.integrate_charge
