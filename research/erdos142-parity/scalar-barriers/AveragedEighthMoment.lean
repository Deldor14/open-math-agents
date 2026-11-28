import Mathlib

/-! The eighth moment of a sum of independent, centered real observations.
Finite coordinate laws may differ. No symmetry or identical distribution
is required. -/

namespace Erdos142EighthMoment
open Finset

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι]

private def multiplicity (w : Fin 8 → ι) (i : ι) :=
  (univ.filter (fun j => w j=i)).card

private noncomputable def repeated (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Finset (Fin 8 → ι) := by
  classical exact univ.filter (fun w => ∀ i, multiplicity w i≠1)

/-- An eight-letter word with no singleton index uses at most four values.
Encoding those values and the eight slot labels gives a uniform cardinal bound. -/
theorem repeated_bound (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (repeated ι).card ≤ Fintype.card ι^4 * 4^8 := by
  classical
  let collect (q : (Fin 4 → ι) × (Fin 8 → Fin 4)) := fun j => q.1 (q.2 j)
  have inside : repeated ι ⊆ univ.image collect := by
    intro w hw
    have no := (mem_filter.mp hw).2
    let S := univ.image w
    have npos {i : ι} (hi : i∈S) : 0 < multiplicity w i := by
      obtain ⟨j,_,rfl⟩ := mem_image.mp hi
      exact card_pos.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
    have total : ∑ i∈S, multiplicity w i=8 := by
      change ∑ i∈S, (univ.filter (fun j => w j=i)).card=8
      rw [sum_card_fiberwise_eq_card_filter]
      have all (j : Fin 8) : w j∈S := mem_image_of_mem _ (mem_univ _)
      simp [all]
    have four : S.card≤4 := by
      have limit := sum_le_sum (fun i (hi : i∈S) => (show 2 ≤ multiplicity w i by
        have := no i; have := npos hi; omega))
      simp only [sum_const,smul_eq_mul,total] at limit
      omega
    obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card ↥S ≤ Fintype.card (Fin 4) by simpa using four)
    let tag (j : Fin 8) : ↥S := ⟨w j,mem_image_of_mem _ (mem_univ _)⟩
    let _ : Nonempty ↥S := ⟨tag 0⟩
    let table (q : Fin 4) : ι := (Function.invFun emb q).val
    refine mem_image.mpr ⟨(table,fun j => emb (tag j)),mem_univ _,?_⟩
    funext j
    exact congrArg Subtype.val (Function.leftInverse_invFun emb.injective (tag j))
  simpa using (card_le_card inside).trans card_image_le

private theorem word_le (x : Fin 8 → ℝ) : ∏ j, x j ≤ ∑ j, x j^8 := by
  obtain ⟨j,_,best⟩ := univ.exists_max_image (fun i => |x i|) univ_nonempty
  have m := prod_le_prod (s:=univ) (fun i _ => abs_nonneg (x i)) best
  have one := single_le_sum (f:=fun i => x i^8) (fun i _ => by positivity) (mem_univ j)
  calc ∏ i, x i ≤ |∏ i, x i| := le_abs_self _
       _ = ∏ i, |x i| := Finset.abs_prod _ _
       _ ≤ _ := m
       _ = x j^8 := by simp [←abs_pow,abs_of_nonneg (show 0≤x j^8 by positivity)]
       _ ≤ _ := one

noncomputable def average (p : ι → Ω → ℝ) (f : (ι → Ω) → ℝ) :=
  ∑ a, (∏ i, p i (a i))*f a

private theorem factor (p X : ι → Ω → ℝ) (w : Fin 8 → ι) :
    average p (fun a => ∏ j, X (w j) (a (w j))) =
    ∏ i, ∑ b, p i b * X i b ^ multiplicity w i := by
  classical
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro a _
  have grouped := prod_fiberwise' (univ : Finset (Fin 8)) w (fun i => X i (a i))
  simp only [prod_const] at grouped
  change (∏ i, X i (a i)^multiplicity w i)=_ at grouped
  change (∏ i, p i (a i))*(∏ j, X (w j) (a (w j))) = _
  rw [←grouped,←prod_mul_distrib]

private theorem single (p X : ι → Ω → ℝ) (total : ∀ i, ∑ b, p i b=1) (i : ι) :
    average p (fun a => X i (a i)^8) = ∑ b, p i b*X i b^8 := by
  classical
  have form := factor p X (fun _ => i)
  simp only [prod_const,card_univ,Fintype.card_fin] at form
  rw [form,prod_eq_single i]
  · simp [multiplicity]
  · intro j _ diff
    simp [multiplicity,Ne.symm diff,total]
  · simp

/-- Centering is used only to cancel words with a singleton. Mixed monomials
are controlled pointwise by a sum of eight pure eighth powers. -/
theorem sum_eighth (p X : ι → Ω → ℝ)
    (pos : ∀ i b, 0≤p i b) (total : ∀ i, ∑ b, p i b=1)
    (center : ∀ i, ∑ b, p i b*X i b=0) {M : ℝ}
    (boundM : 0≤M) (mom : ∀ i, ∑ b, p i b*X i b^8≤M) :
    average p (fun a => (∑ i, X i (a i))^8) ≤ (8*4^8:ℝ)*(Fintype.card ι:ℝ)^4*M := by
  classical
  let mixed (w : Fin 8 → ι) := average p (fun a => ∏ j, X (w j) (a (w j)))
  have words (a : ι → Ω) : (∑ i, X i (a i))^8 =
      ∑ w : Fin 8 → ι, ∏ j, X (w j) (a (w j)) := by
    have h := Fintype.prod_sum (fun (_ : Fin 8) (i : ι) => X i (a i))
    simpa using h
  have expand : average p (fun a => (∑ i, X i (a i))^8) = ∑ w∈repeated ι, mixed w := by
    unfold average
    simp_rw [words,mul_sum]
    rw [sum_comm]
    symm
    apply sum_subset (subset_univ _)
    intro w _ omitted
    obtain ⟨i,hi⟩ : ∃ i, multiplicity w i=1 := by
      by_contra! h; exact omitted (mem_filter.mpr ⟨mem_univ _,h⟩)
    change average p _=0
    rw [factor]
    apply prod_eq_zero (mem_univ i)
    simpa [hi] using center i
  have each (w : Fin 8 → ι) : mixed w ≤ 8*M := by
    have comp (a : ι → Ω) := mul_le_mul_of_nonneg_left
      (word_le (fun j => X (w j) (a (w j)))) (prod_nonneg (s:=univ) fun i _ => pos i (a i))
    have h := sum_le_sum (fun a (_ : a∈(univ : Finset (ι → Ω))) => comp a)
    simp_rw [mul_sum] at h
    rw [sum_comm] at h
    change mixed w ≤ ∑ j, average p (fun a => X (w j) (a (w j))^8) at h
    simp_rw [single p X total] at h
    have upper := sum_le_sum (s:=univ) (fun j _ => mom (w j))
    exact h.trans (by simpa using upper)
  rw [expand]
  have sum := sum_le_sum (s:=repeated ι) (fun w _ => each w)
  have num : ((repeated ι).card:ℝ) ≤ (Fintype.card ι:ℝ)^4*4^8 := by exact_mod_cast repeated_bound ι
  simp only [sum_const,nsmul_eq_mul] at sum
  exact sum.trans ((mul_le_mul_of_nonneg_right num (by positivity : 0≤8*M)).trans_eq (by ring))

/-- For the average rather than the sum, each level gains a factor m⁻⁴. -/
theorem mean_eighth (p X : ι → Ω → ℝ) (n : 0<Fintype.card ι)
    (pos : ∀ i b, 0≤p i b) (total : ∀ i, ∑ b, p i b=1)
    (center : ∀ i, ∑ b, p i b*X i b=0) {M : ℝ}
    (boundM : 0≤M) (mom : ∀ i, ∑ b, p i b*X i b^8≤M) :
    average p (fun a => ((∑ i, X i (a i))/(Fintype.card ι:ℝ))^8) ≤
      (8*4^8:ℝ)*M/(Fintype.card ι:ℝ)^4 := by
  have h := sum_eighth p X pos total center boundM mom
  have positive : (0:ℝ)<Fintype.card ι := by exact_mod_cast n
  have split : average p (fun a => ((∑ i, X i (a i))/(Fintype.card ι:ℝ))^8) =
      average p (fun a => (∑ i, X i (a i))^8)/(Fintype.card ι:ℝ)^8 := by
    unfold average
    conv_rhs => rw [Finset.sum_div]
    apply sum_congr rfl
    intro a _
    simp only [div_pow,mul_div_assoc]
  rw [split]
  apply (div_le_iff₀ (pow_pos positive 8)).mpr
  exact h.trans_eq (by field_simp)

#print axioms mean_eighth
#print axioms repeated_bound
#print axioms sum_eighth
end Erdos142EighthMoment
