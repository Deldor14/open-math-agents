import Mathlib

/-! A scalar coincidence theorem for the lower-semicontinuous fixed point
question of Xian Wu (MathOverflow 61309). The argument works for every
continuous real observable on any nonempty compact connected domain. -/
namespace Deldor14.ScalarCoincidence
open Set
variable {E : Type*} [TopologicalSpace E]
def LowerOn (X : Set E) (F : E → Set E) : Prop :=
  ∀ U : Set E, IsOpen U → ∃ V : Set E, IsOpen V ∧ {x ∈ X | (F x ∩ U).Nonempty} = V ∩ X

private lemma hit_open {X : Set E} {F : E → Set E} (h : LowerOn X F)
    (U : Set E) (hu : IsOpen U) : IsOpen {x : X | (F x.val ∩ U).Nonempty} := by
  obtain ⟨V,hV,e⟩ := h U hu
  have eq : {x : X | (F x.val ∩ U).Nonempty}=Subtype.val ⁻¹' V := by
    ext x
    have ex := Set.ext_iff.mp e x.val
    simpa [x.property] using ex
  rw [eq]
  exact hV.preimage continuous_subtype_val

private lemma lower_open {X : Set E} {F : E → Set E} (h : LowerOn X F)
    (f : E → ℝ) (hf : Continuous f) :
    IsOpen {x : X | ∃ y ∈ F x.val, f y < f x.val} := by
  have eq : {x : X | ∃ y ∈ F x.val, f y < f x.val} =
      ⋃ r : ℝ, {x : X | (F x.val ∩ (f ⁻¹' Iio r)).Nonempty} ∩ {x : X | r < f x.val} := by
    ext x
    simp only [mem_setOf_eq,mem_iUnion,mem_inter_iff]
    constructor
    · rintro ⟨y,hy,lt⟩
      obtain ⟨r,hr,hs⟩ := exists_between lt
      exact ⟨r,⟨y,hy,hr⟩,hs⟩
    · rintro ⟨r,⟨y,hy,h1⟩,h2⟩
      exact ⟨y,hy,lt_trans h1 h2⟩
  rw [eq]
  exact isOpen_iUnion fun r => (hit_open h _ (isOpen_Iio.preimage hf)).inter
    (isOpen_lt continuous_const (hf.comp continuous_subtype_val))

theorem scalar_coincidence {X : Set E} {F : E → Set E}
    (ne : X.Nonempty) (hk : IsCompact X) (hc : IsPreconnected X)
    (val : ∀ x ∈ X, (F x).Nonempty ∧ F x ⊆ X ∧ IsPreconnected (F x))
    (lsc : LowerOn X F) (f : E → ℝ) (hf : Continuous f) :
    ∃ x ∈ X, ∃ y ∈ F x, f y=f x := by
  classical
  by_contra! no
  let L : Set X := {x | ∃ y ∈ F x.val, f y < f x.val}
  let U : Set X := {x | ∃ y ∈ F x.val, f x.val < f y}
  have hl : IsOpen L := lower_open lsc f hf
  have hu : IsOpen U := by simpa [U] using lower_open lsc (fun x => -f x) hf.neg
  have cover : univ ⊆ L ∪ U := by
    intro x _
    obtain ⟨y,hy⟩ := (val x x.property).1
    rcases lt_or_gt_of_ne (no x x.property y hy) with lt | gt
    · exact Or.inl ⟨y,hy,lt⟩
    · exact Or.inr ⟨y,hy,gt⟩
  obtain ⟨lo,hlo,small⟩ := hk.exists_isMinOn ne hf.continuousOn
  obtain ⟨hi,hhi,large⟩ := hk.exists_isMaxOn ne hf.continuousOn
  obtain ⟨y,hy⟩ := (val hi hhi).1
  obtain ⟨z,hz⟩ := (val lo hlo).1
  have left : (univ ∩ L).Nonempty :=
    ⟨⟨hi,hhi⟩,mem_univ _,y,hy,lt_of_le_of_ne (large ((val hi hhi).2.1 hy)) (no hi hhi y hy)⟩
  have right : (univ ∩ U).Nonempty :=
    ⟨⟨lo,hlo⟩,mem_univ _,z,hz,lt_of_le_of_ne (small ((val lo hlo).2.1 hz)) (no lo hlo z hz).symm⟩
  letI : PreconnectedSpace X := isPreconnected_iff_preconnectedSpace.mp hc
  obtain ⟨x,_,⟨b,hb,lb⟩,⟨c,hc',lt⟩⟩ := isPreconnected_univ L U hl hu cover left right
  have conn := ((val x x.property).2.2.image f hf.continuousOn).ordConnected
  obtain ⟨w,hw,eq⟩ := conn.out (mem_image_of_mem f hb) (mem_image_of_mem f hc') ⟨lb.le,lt.le⟩
  exact no x x.property w hw eq

theorem scalar_fixed {X : Set ℝ} {F : ℝ → Set ℝ} (ne : X.Nonempty)
    (hk : IsCompact X) (hc : Convex ℝ X)
    (v : ∀ x∈X, (F x).Nonempty ∧ F x ⊆ X ∧ Convex ℝ (F x))
    (h : LowerOn X F) : ∃ x ∈ X, x ∈ F x := by
  obtain ⟨x,hx,y,hy,e⟩ := scalar_coincidence ne hk hc.isPreconnected
    (fun x hx => ⟨(v x hx).1,(v x hx).2.1,(v x hx).2.2.isPreconnected⟩) h id continuous_id
  exact ⟨x,hx,(show y=x from e) ▸ hy⟩
end Deldor14.ScalarCoincidence
#print axioms Deldor14.ScalarCoincidence.scalar_coincidence
#print axioms Deldor14.ScalarCoincidence.scalar_fixed
