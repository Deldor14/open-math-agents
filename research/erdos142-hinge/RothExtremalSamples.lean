import Mathlib

open Finset
namespace Erdos142ExtremalSamples

variable {α : Type*} [DecidableEq α]

/-- All size-s samples from A contained in a container missing at least d sites of A. -/
def badSamples (A : Finset α) (family : Finset (Finset α)) (s d : ℕ) :
    Finset (Finset α) :=
  (family.filter (fun C => d ≤ (A \ C).card)).biUnion
    (fun C => (A ∩ C).powersetCard s)

theorem bad_sample_count (A : Finset α) (family : Finset (Finset α)) (s d : ℕ) :
    (badSamples A family s d).card ≤ family.card * (A.card - d).choose s := by
  classical
  let F := family.filter (fun C => d ≤ (A \ C).card)
  calc
    _ ≤ ∑ C ∈ F, ((A ∩ C).powersetCard s).card := card_biUnion_le
    _ ≤ ∑ _C ∈ F, (A.card - d).choose s := by
      apply sum_le_sum
      intro C hC
      have hd : d ≤ (A \ C).card := (mem_filter.mp hC).2
      have h := card_sdiff_add_card_inter A C
      rw [card_powersetCard]
      exact Nat.choose_le_choose _ (by omega)
    _ = F.card * (A.card - d).choose s := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (card_le_card (filter_subset _ _))

theorem compatible_container {A S B C : Finset α} {family : Finset (Finset α)}
    {s d : ℕ} (size : S.card = s) (sample : S ⊆ A) (compatible : S ⊆ B)
    (covered : B ⊆ C) (member : C ∈ family) (good : S ∉ badSamples A family s d) :
    (A \ C).card < d := by
  classical
  by_contra! large
  apply good
  exact mem_biUnion.mpr ⟨C, mem_filter.mpr ⟨member, large⟩,
    mem_powersetCard.mpr ⟨subset_inter sample (compatible.trans covered), size⟩⟩

theorem outside_bound {A B C : Finset α} {d z : ℕ}
    (covered : B ⊆ C) (small : C.card ≤ A.card + z) (miss : (A \ C).card ≤ d) :
    (B \ A).card ≤ z + d := by
  have sub : B \ A ⊆ C \ A := by
    intro x hx
    exact mem_sdiff.mpr ⟨covered (mem_sdiff.mp hx).1, (mem_sdiff.mp hx).2⟩
  have h := card_le_card sub
  have h₁ := card_sdiff_add_card_inter A C
  have h₂ := card_sdiff_add_card_inter C A
  rw [inter_comm C A] at h₂
  omega

/-- The whole family of sets with a consistent sample is controlled at once. -/
theorem sample_reconstruction {A S : Finset α} {family : Finset (Finset α)}
    {s d z : ℕ} (size : S.card = s) (sample : S ⊆ A)
    (small : ∀ C ∈ family, C.card ≤ A.card + z)
    (good : S ∉ badSamples A family s d) (B : Finset α)
    (compatible : S ⊆ B) (cover : ∃ C ∈ family, B ⊆ C) :
    (B \ A).card ≤ z + d := by
  obtain ⟨C, hC, hBC⟩ := cover
  exact outside_bound hBC (small C hC)
    (compatible_container size sample compatible hBC hC good).le

/-- A finite family of containers bounds the count at any prescribed rank. -/
theorem layer_bounds {A : Finset α} {family admissible : Finset (Finset α)} {s b : ℕ}
    (down : A.powersetCard s ⊆ admissible)
    (rank : ∀ B ∈ admissible, B.card = s)
    (cover : ∀ B ∈ admissible, ∃ C ∈ family, B ⊆ C)
    (cap : ∀ C ∈ family, C.card ≤ b) :
    A.card.choose s ≤ admissible.card ∧ admissible.card ≤ family.card * b.choose s := by
  classical
  constructor
  · simpa using card_le_card down
  · have contain : admissible ⊆ family.biUnion (fun C => C.powersetCard s) := by
      intro B hB
      obtain ⟨C, hC, sub⟩ := cover B hB
      exact mem_biUnion.mpr ⟨C, hC, mem_powersetCard.mpr ⟨sub, rank B hB⟩⟩
    calc
      _ ≤ _ := card_le_card contain
      _ ≤ ∑ C ∈ family, (C.powersetCard s).card := card_biUnion_le
      _ ≤ ∑ _C ∈ family, b.choose s := by
        apply sum_le_sum
        intro C hC
        simpa using Nat.choose_le_choose s (cap C hC)
      _ = _ := by simp

theorem product_choices_le {ι : Type*} (I : Finset ι) (f : ι → ℕ)
    (positive : ∀ i ∈ I, 1 ≤ f i) :
    ∏ i ∈ I, f i ≤ 2 ^ (∑ i ∈ I, (f i - 1)) := by
  classical
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod'
  intro i hi
  have h : f i - 1 < 2 ^ (f i - 1) := Nat.lt_two_pow_self
  have := positive i hi
  omega

omit [DecidableEq α] in
theorem overlap_budget {ι : Type*} (I : Finset ι) (C : Finset α)
    (inCopy : ι → α → Prop) [DecidableRel inCopy] (weight : ι → ℝ) {p : ℝ}
    (hp : 0 ≤ p) (hweight : ∀ i ∈ I, weight i ≤ p) :
    (∑ i ∈ I, weight i * ((C.filter (inCopy i)).card : ℝ)) ≤
      p * (C.card + ∑ y ∈ C, (((I.filter (fun i => inCopy i y)).card - 1 : ℕ) : ℝ)) := by
  classical
  have hsum (i : ι) : weight i * ((C.filter (inCopy i)).card : ℝ) =
      ∑ y ∈ C, (if inCopy i y then weight i else 0) := by
    rw [← sum_filter]
    simp [mul_comm]
  simp_rw [hsum]
  rw [sum_comm]
  calc
    _ ≤ ∑ y ∈ C, (p * (1 + (((I.filter (fun i => inCopy i y)).card - 1 : ℕ) : ℝ))) := by
      apply sum_le_sum
      intro y _
      rw [← sum_filter]
      let J := I.filter (fun i => inCopy i y)
      have hn : J.card ≤ 1 + (J.card - 1) := by omega
      calc
        _ ≤ ∑ _i ∈ J, p := sum_le_sum (fun i hi => hweight i (mem_filter.mp hi).1)
        _ = p * (J.card : ℝ) := by simp [mul_comm]
        _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hp
    _ = _ := by rw [← mul_sum]; simp [sum_add_distrib]

theorem sum_overlap_directions (A : Finset ℤ) (T : Finset ℤ) (c : ℤ) (r : ℕ)
    (rows : ∀ a ∈ A, (T.filter (fun t => a + c*t ∈ A)).card ≤ r) :
    ∑ t ∈ T, (A.filter (fun a => a + c*t ∈ A)).card ≤ A.card * r := by
  classical
  simp_rw [card_filter]
  rw [sum_comm]
  calc
    _ ≤ ∑ _a ∈ A, r := by
      apply sum_le_sum
      intro a ha
      rw [← card_filter]
      exact rows a ha
    _ = _ := by simp

/-- Two ordered distinct sites determine an invertible affine map over a field. -/
theorem unique_affine_pair {F : Type*} [Field F] {i j y z : F}
    (ij : i ≠ j) (yz : y ≠ z) :
    ∃! ab : F × F, ab.1 ≠ 0 ∧ ab.1 * i + ab.2 = y ∧ ab.1 * j + ab.2 = z := by
  let a := (z-y)/(j-i)
  have denom : j-i ≠ 0 := sub_ne_zero.mpr ij.symm
  have ha : a ≠ 0 := div_ne_zero (sub_ne_zero.mpr yz.symm) denom
  have slope : a*(j-i) = z-y := div_mul_cancel₀ _ denom
  refine ⟨(a,y-a*i), ⟨ha, by dsimp; ring, by dsimp; linear_combination slope⟩, ?_⟩
  rintro ⟨u,v⟩ ⟨_,hy,hz⟩
  change u*i+v=y at hy
  change u*j+v=z at hz
  have hu : u = a := (eq_div_iff denom).mpr (by linear_combination hz-hy)
  subst u
  exact Prod.ext rfl (by change v=y-a*i; linear_combination hy)

/-- Absorption after counting the point and pair incidences on the affine line. -/
theorem affine_cover_absorption (points edges ell P R weight : ℝ)
    (hEll : 0 < ell) (hP : 1 < P) (hC : 0 ≤ points) (hL : 1 ≤ ell)
    (count : points*ell*(P-1) ≤ R*P*(P-1) + edges*ell*(ell-1))
    (cheap : edges ≤ points*weight) (small : 2*weight*(ell-1) ≤ P-1) :
    points*ell ≤ 2*P*R := by
  have h₁ := mul_le_mul_of_nonneg_right cheap (show 0 ≤ ell*(ell-1) by positivity)
  have h₂ := mul_le_mul_of_nonneg_right small (show 0 ≤ points*ell by positivity)
  apply le_of_mul_le_mul_right (a := P-1) (by nlinarith [h₁,h₂]) (by linarith)

#print axioms bad_sample_count
#print axioms compatible_container
#print axioms outside_bound
#print axioms sample_reconstruction
#print axioms layer_bounds
#print axioms product_choices_le
#print axioms overlap_budget
#print axioms sum_overlap_directions
#print axioms unique_affine_pair
#print axioms affine_cover_absorption

end Erdos142ExtremalSamples
