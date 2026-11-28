import RothAffineVariance

open Finset
namespace Erdos142AffineVariance

/-- One nonzero slope and shift work for an arbitrary weighted list of
    centered tests, with the exact average loss on the right. -/
theorem select_tests {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
    (A : Finset F) (T : Finset ι) (h : ι → F → ℝ) (w : ι → ℝ)
    (zero : ∀ i ∈ T, ∑ x : F, h i x=0) :
    ∃ a : F, a≠0 ∧ ∃ b : F,
      ((Fintype.card F:ℝ)-1)*(Fintype.card F)*
        (∑ i ∈ T, w i*(∑ x ∈ A, h i (a*x+b))^2) ≤
      (A.card:ℝ)*(Fintype.card F-A.card)*(∑ i ∈ T, w i*∑ z : F, (h i z)^2) := by
  classical
  let G := (univ.erase (0:F)) ×ˢ (univ : Finset F)
  let cost (ab : F × F) := ∑ i ∈ T, w i*(∑ x ∈ A, h i (ab.1*x+ab.2))^2
  have ne : G.Nonempty := ⟨(1,0),mem_product.mpr ⟨mem_erase.mpr ⟨one_ne_zero,mem_univ _⟩,mem_univ _⟩⟩
  obtain ⟨ab,mem,small⟩ := exists_min_image G cost ne
  have all := sum_le_sum (fun x hx => small x hx)
  have id : ∑ ab ∈ G, cost ab =
      (A.card:ℝ)*(Fintype.card F-A.card)*(∑ i ∈ T, w i*∑ z : F, (h i z)^2) := by
    dsimp only [cost]
    rw [sum_comm,mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [← mul_sum]
    have var := variance A (h i) (zero _ hi)
    dsimp only [G]
    rw [sum_product]
    rw [var]
    ring
  have size : (G.card:ℝ)=((Fintype.card F:ℝ)-1)*(Fintype.card F) := by
    simp only [G,card_product,card_erase_of_mem (mem_univ _),card_univ,Nat.cast_mul]
    rw [Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨(0:F)⟩),Nat.cast_one]
  refine ⟨ab.1,(mem_erase.mp (mem_product.mp mem).1).1,ab.2,?_⟩
  rw [← size,← id]
  simpa [nsmul_eq_mul,cost] using all

/-- Sum of squares for the centered indicator of a single cell. -/
theorem cell_moment {F : Type*} [Fintype F] [Nonempty F] [DecidableEq F] (C : Finset F) :
    ∑ z : F, ((if z ∈ C then (1:ℝ) else 0)-(C.card:ℝ)/Fintype.card F)^2 =
      C.card*(1-(C.card:ℝ)/Fintype.card F) := by
  classical
  have ind : ∑ z : F, (if z ∈ C then (1:ℝ) else 0)=C.card := by simp
  have sqind (z : F) : (if z ∈ C then (1:ℝ) else 0)^2=(if z ∈ C then 1 else 0) := by
    split <;> norm_num
  simp_rw [sub_sq,sqind]
  rw [sum_add_distrib,sum_sub_distrib,← sum_mul,← mul_sum,ind]
  simp only [sum_const,card_univ,nsmul_eq_mul]
  have fp : (0:ℝ)<Fintype.card F := by exact_mod_cast Fintype.card_pos
  field_simp
  ring

#print axioms select_tests
#print axioms cell_moment
end Erdos142AffineVariance
