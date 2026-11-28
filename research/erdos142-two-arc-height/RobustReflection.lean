import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

open Set MeasureTheory MeasureTheory.Measure Metric
open scoped ENNReal

namespace Erdos142Reflection

/-- Removing points from an envelope costs at most twice their measure in its
intersection with a measure-preserving reflection (or any preserving map). -/
theorem deletion {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {E U : Set α} (hE : NullMeasurableSet E μ) (hU : NullMeasurableSet U μ)
    (hsub : U⊆E) {r : α→α} (hr : MeasurePreserving r μ μ) :
    μ.real (E ∩ r ⁻¹' E) ≤ μ.real (U ∩ r ⁻¹' U) + 2*(μ.real E-μ.real U) := by
  let H := E \ U
  have hs : E ∩ r ⁻¹' E ⊆ ((U ∩ r ⁻¹' U) ∪ H) ∪ r ⁻¹' H := by
    intro x hx
    by_cases h₁ : x∈U
    · by_cases h₂ : r x∈U
      · exact Or.inl (Or.inl ⟨h₁,h₂⟩)
      · exact Or.inr ⟨hx.2,h₂⟩
    · exact Or.inl (Or.inr ⟨hx.1,h₁⟩)
  have heq : μ.real (r ⁻¹' H) = μ.real H := by
    unfold Measure.real
    rw [hr.measure_preimage (hE.diff hU)]
  have hmass := measureReal_inter_add_sdiff₀ (s:=E) hU
  rw [inter_eq_right.mpr hsub] at hmass
  calc
    _ ≤ μ.real (((U ∩ r ⁻¹' U) ∪ H) ∪ r ⁻¹' H) := measureReal_mono hs
    _ ≤ μ.real ((U ∩ r ⁻¹' U) ∪ H) + μ.real (r ⁻¹' H) := measureReal_union_le _ _
    _ ≤ μ.real (U ∩ r ⁻¹' U) + μ.real H + μ.real (r ⁻¹' H) := by gcongr; apply measureReal_union_le
    _ = _ := by change μ.real _ + μ.real (E \ U) + μ.real (r ⁻¹' H) = _; rw [heq]; dsimp [H]; linarith

abbrev Circle := AddCircle (1:ℝ)

/-- Exact Haar law for the near-zero costs of a physical progression with
middle y. The reflected endpoint is 2y−x, so the doubled endpoint difference
is 4(x−y). -/
theorem small_cost (y : Circle) {r : ℝ} (hr : 0≤r) :
    volume.real {x : Circle | ‖(4:ℤ) • (x-y)‖ ≤ r} ≤ 2*r := by
  have hp : MeasurePreserving (fun x : Circle => (4:ℤ) • (x-y)) volume volume :=
    (measurePreserving_zsmul volume (by norm_num : (4:ℤ)≠0)).comp (measurePreserving_sub_right volume y)
  have eqn : {x : Circle | ‖(4:ℤ) • (x-y)‖ ≤ r} =
      (fun x : Circle => (4:ℤ) • (x-y)) ⁻¹' closedBall 0 r := by
    ext x; simp [mem_closedBall]
  rw [eqn,measureReal_def,hp.measure_preimage measurableSet_closedBall.nullMeasurableSet,
    AddCircle.volume_closedBall,ENNReal.toReal_ofReal (by positivity)]
  exact min_le_right _ _

/-- Quantitative measurable-fibre obstruction. A midpoint inequality may fail
on a set of endpoints of measure h at each middle, and may have defect error ε. -/
theorem robust_row {E U : Set Circle} (hE : NullMeasurableSet E volume)
    (hU : NullMeasurableSet U volume) (hsub : U⊆E) (hU0 : U.Nonempty)
    (F : Circle → ℝ) (hbounded : BddAbove (F '' U)) (bad : Circle → Set Circle)
    {B h ε c : ℝ} (hc : 0<c) (hε : 0≤ε)
    (hbad : ∀y∈U, volume.real (bad y) ≤ h)
    (henv : ∀ y∈U, 2*(volume.real E-B) ≤
      volume.real (E ∩ (fun x => y+y-x) ⁻¹' E))
    (hdef : ∀y∈U, ∀x∈U, y+y-x∈U → x∉bad y →
      c*‖(4:ℤ) • (x-y)‖^2-ε ≤ F x+F (y+y-x)-2*F y) :
    volume.real U ≤ B+Real.sqrt (ε/c)+h/2 := by
  apply le_of_forall_pos_le_add
  intro t ht
  let r := Real.sqrt (ε/c)+t
  have hroot := Real.sq_sqrt (div_nonneg hε hc.le)
  have hpos : 0<r := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) ht
  have hstrict : ε<c*r^2 := by
    have hh : Real.sqrt (ε/c)<r := by dsimp [r]; linarith
    have hs : (Real.sqrt (ε/c))^2<r^2 := by gcongr
    rw [hroot] at hs
    exact (div_lt_iff₀ hc).mp hs |> fun z => by linarith
  obtain ⟨v,⟨y,hy,rfl⟩,hnear⟩ :=
    (lt_csSup_iff hbounded (hU0.image F)).1
      (show sSup (F '' U)-(c*r^2-ε)/2 < sSup (F '' U) by linarith)
  let f := fun x : Circle => y+y-x
  have hp : MeasurePreserving f volume volume := by
    simpa [f,Function.comp_def,sub_eq_add_neg] using
      (measurePreserving_add_left (volume : Measure Circle) (y+y)).comp (measurePreserving_neg volume)
  have hcontain : U ∩ f ⁻¹' U ⊆ {x : Circle | ‖(4:ℤ) • (x-y)‖≤r} ∪ bad y := by
    intro x hx
    by_cases hb : x∈bad y
    · exact Or.inr hb
    · left
      have hscore := hdef y hy x hx.1 hx.2 hb
      have ha := le_csSup hbounded (mem_image_of_mem F hx.1)
      have hz := le_csSup hbounded (mem_image_of_mem F hx.2)
      change ‖(4:ℤ) • (x-y)‖≤r
      by_contra! hneg
      have hsq : r^2 < ‖(4:ℤ) • (x-y)‖^2 := by gcongr
      have hmul := mul_lt_mul_of_pos_left hsq hc
      change F (y+y-x) ≤ _ at hz
      linarith
  have submass := (measureReal_mono (μ:=volume) hcontain).trans (measureReal_union_le _ _)
  have hdel := deletion volume hE hU hsub hp
  have henvy := henv y hy
  change 2*(volume.real E-B) ≤ volume.real (E ∩ f ⁻¹' E) at henvy
  have hvol := small_cost y hpos.le
  have hb := hbad y hy
  dsimp [r] at hvol
  linarith

end Erdos142Reflection

#print axioms Erdos142Reflection.deletion
#print axioms Erdos142Reflection.small_cost
#print axioms Erdos142Reflection.robust_row
