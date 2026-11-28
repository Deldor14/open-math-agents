import Mathlib

open Finset
namespace Erdos142CircleEnergy

/-- Delete at most one site for every edge contained in a sample. -/
theorem delete_active {α : Type*} [DecidableEq α] (S : Finset α) (E : Finset (Finset α))
    (pick : Finset α → α) (valid : ∀ e ∈ E, pick e ∈ e) :
    ∃ T ⊆ S, (∀ e ∈ E, ¬ e ⊆ T) ∧
      S.card ≤ T.card + (E.filter (fun e => e ⊆ S)).card := by
  classical
  let active := E.filter (fun e => e ⊆ S)
  let removed := active.image pick
  have sub : removed ⊆ S := by
    intro x hx
    obtain ⟨e,he,rfl⟩ := mem_image.mp hx
    exact (mem_filter.mp he).2 (valid e (mem_filter.mp he).1)
  refine ⟨S \ removed, sdiff_subset, ?_, ?_⟩
  · intro e he h
    have ea : e ∈ active := mem_filter.mpr ⟨he, h.trans sdiff_subset⟩
    exact (mem_sdiff.mp (h (valid e he))).2 (mem_image_of_mem pick ea)
  · have eq := card_sdiff_add_card_eq_card sub
    have le : removed.card ≤ active.card := card_image_le
    change S.card ≤ (S \ removed).card + active.card
    omega

/-- Average over arbitrary finite weighted samples. A size bound for every
free subset gives the deletion inequality for those actual edge incidences. -/
theorem average_deletion {α β : Type*} [DecidableEq α]
    (Ω : Finset β) (weight : β → ℝ) (S : β → Finset α) (E : Finset (Finset α))
    (pick : Finset α → α) (valid : ∀ e ∈ E, pick e ∈ e)
    (hp : ∀ z ∈ Ω, 0 ≤ weight z) (total : ∑ z ∈ Ω, weight z = 1)
    (r : ℕ) (rank : ∀ z ∈ Ω, ∀ T ⊆ S z, (∀ e ∈ E, ¬ e ⊆ T) → T.card ≤ r) :
    ∑ z ∈ Ω, weight z * ((S z).card : ℝ) ≤
      r + ∑ z ∈ Ω, weight z * ((E.filter (fun e => e ⊆ S z)).card : ℝ) := by
  calc
    _ ≤ ∑ z ∈ Ω, weight z * ((r : ℝ) + (E.filter (fun e => e ⊆ S z)).card) := by
      apply sum_le_sum
      intro z hz
      obtain ⟨T,sub,free,h⟩ := delete_active (S z) E pick valid
      apply mul_le_mul_of_nonneg_left _ (hp z hz)
      exact_mod_cast (h.trans (Nat.add_le_add_right (rank z hz T sub free) _))
    _ = _ := by simp_rw [mul_add]; rw [sum_add_distrib, ← sum_mul, total, one_mul]

/-- Sharp cubic cost of truncating one nonnegative site at height one. -/
theorem cubic_clip {x : ℝ} (hx : 0 ≤ x) : x ≤ min x 1 + 4 / 27 * x^3 := by
  by_cases h : x ≤ 1
  · rw [min_eq_left h]
    nlinarith [pow_nonneg hx 3]
  · rw [min_eq_right (le_of_not_ge h)]
    nlinarith [mul_nonneg (show 0 ≤ x+3 by linarith) (sq_nonneg (2*x-3))]

/-- Optimization over clipping heights of the affine sampling inequality. -/
theorem cubic_transfer {m δ J V : ℝ} (hm : 0 < m) (hd : 0 < δ)
    (clip : ∀ t : ℝ, 0 < t → m*t^2 ≤ δ*t^3 + (4/27)*J + V) :
    m^3 ≤ δ^2 * (J + 27/4*V) := by
  let t := 2*m/(3*δ)
  have ht : 0 < t := by dsimp [t]; positivity
  have e : δ*t = (2/3)*m := by dsimp [t]; field_simp
  have h := mul_le_mul_of_nonneg_left (clip t ht) (sq_nonneg δ)
  calc
    m^3 = (27/4)*(δ^2*(m*t^2-δ*t^3)) := by
      calc
        _ = (27/4)*(m*(δ*t)^2-(δ*t)^3) := by rw [e]; ring
        _ = _ := by ring
    _ ≤ _ := by linarith only [show δ^2*(m*t^2-δ*t^3) ≤ δ^2*((4/27)*J+V) by linarith only [h] ]

open MeasureTheory

/-- The continuum cubic inequality on any finite measure space, once affine
sampling bounds the integrals of the clipped profiles. -/
theorem integral_transfer {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hf : Integrable f μ)
    (hn : ∀ᵐ x ∂μ, 0 ≤ f x) (hj : Integrable (fun x => f x ^ 3) μ)
    (hm : 0 < ∫ x, f x ∂μ) {δ V : ℝ} (hd : 0 < δ)
    (hc : ∀ t : ℝ, 0 < t → Integrable (fun x => min (f x) t) μ)
    (sampling : ∀ t : ℝ, 0 < t →
      (∫ x, min (f x) t ∂μ) * t^2 ≤ δ*t^3 + V) :
    (∫ x, f x ∂μ)^3 ≤ δ^2*((∫ x, (f x)^3 ∂μ) + 27/4*V) := by
  apply cubic_transfer hm hd
  intro t ht
  have point : ∀ᵐ x ∂μ, t^2*f x ≤ t^2*min (f x) t + (4/27)*(f x)^3 := by
    filter_upwards [hn] with x hx
    by_cases h : f x ≤ t
    · rw [min_eq_left h]
      nlinarith [pow_nonneg hx 3]
    · rw [min_eq_right (le_of_not_ge h)]
      nlinarith [mul_nonneg (show 0 ≤ f x+3*t by linarith) (sq_nonneg (2*f x-3*t))]
  have h := integral_mono_ae (hf.const_mul (t^2))
    (((hc t ht).const_mul (t^2)).add (hj.const_mul (4/27))) point
  simp only [Pi.add_apply] at h
  rw [integral_add ((hc t ht).const_mul (t^2)) (hj.const_mul (4/27))] at h
  simp only [integral_const_mul] at h
  linarith [sampling t ht]

/-- A small total correlation bounds the number of periods whose translations
give less than the stated loss in the correlation integral. -/
theorem period_count {α : Type*} (G P : Finset α) (hP : P ⊆ G)
    (corr : α → ℝ) (nonneg : ∀ d ∈ G, 0 ≤ corr d)
    {mass : ℝ} (good : ∀ d ∈ P, mass/2 ≤ corr d) :
    (P.card : ℝ)*mass ≤ 2*∑ d ∈ G, corr d := by
  have h : (P.card : ℝ)*(mass/2) ≤ ∑ d ∈ P, corr d := by
    simpa using (sum_le_sum good)
  have s := sum_le_sum_of_subset_of_nonneg hP (fun d hd _ => nonneg d hd)
  linarith

/-- Quantitative loss bound for any competitor close to the energy infimum.
The value at half the penalty controls the progression part alone. -/
theorem two_scale_loss {n J L E small ε v : ℝ} 
    (close : J+n*L ≤ (1+ε)*E) (half : small ≤ J+(n/2)*L)
    (change : E-small ≤ v*E) : n*L ≤ 2*(ε+v)*E := by
  linarith

#print axioms delete_active
#print axioms average_deletion
#print axioms cubic_clip
#print axioms cubic_transfer
#print axioms integral_transfer
#print axioms period_count
#print axioms two_scale_loss
end Erdos142CircleEnergy
