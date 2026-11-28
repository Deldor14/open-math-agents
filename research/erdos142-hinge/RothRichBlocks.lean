import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Finset
namespace Erdos142RichBlocks

/-- Pair-overlap bound for a family of large subsets of a fixed finite set. -/
theorem bonferroni {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (B : ι → Finset α) (t c : ℕ) (I : Finset ι)
    (large : ∀ i ∈ I, t≤(B i).card)
    (overlap : ∀ i ∈ I, ∀ j ∈ I, i≠j → ((B i) ∩ (B j)).card ≤ c) :
    I.card*t ≤ (I.biUnion B).card + I.card.choose 2*c := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I fresh ih =>
    have prev := ih (fun j hj => large j (mem_insert_of_mem hj))
      (fun j hj k hk ne => overlap j (mem_insert_of_mem hj) k (mem_insert_of_mem hk) ne)
    have cover : B i ∩ I.biUnion B = I.biUnion (fun j => B i ∩ B j) := by
      ext x
      simp only [mem_inter,mem_biUnion]
      constructor
      · rintro ⟨hx,j,hj,hm⟩
        exact ⟨j,hj,hx,hm⟩
      · rintro ⟨j,hj,hx,hm⟩
        exact ⟨hx,j,hj,hm⟩
    have cap : (B i ∩ I.biUnion B).card ≤ I.card*c := calc
      _ = (I.biUnion (fun j => B i ∩ B j)).card := by rw [cover]
      _ ≤ ∑ j ∈ I, (B i ∩ B j).card := card_biUnion_le
      _ ≤ ∑ _j ∈ I, c := sum_le_sum (fun j hj => overlap i (mem_insert_self _ _)
        j (mem_insert_of_mem hj) (fun eq => fresh (eq ▸ hj)))
      _ = _ := by simp
    have add := card_union_add_card_inter (B i) (I.biUnion B)
    have big := large i (mem_insert_self _ _)
    rw [card_insert_of_notMem fresh,biUnion_insert,Nat.add_mul,Nat.one_mul]
    have choose : (I.card+1).choose 2=I.card+I.card.choose 2 := by
      rw [Nat.choose_succ_succ,Nat.choose_one_right]
    rw [choose,Nat.add_mul]
    omega

/-- Bound the size of a family of representatives by testing one fixed subfamily size. -/
theorem representative_count {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (B : ι → Finset α) (C : Finset α) (I : Finset ι) {t c k : ℕ}
    (contained : ∀ i ∈ I, B i ⊆ C) (large : ∀ i ∈ I, t≤(B i).card)
    (overlap : ∀ i ∈ I, ∀ j ∈ I, i≠j → ((B i) ∩ (B j)).card ≤ c)
    (test : C.card+k.choose 2*c<k*t) : I.card<k := by
  by_contra! enough
  obtain ⟨J,sub,size⟩ := exists_subset_card_eq enough
  have count := bonferroni B t c J (fun j hj => large j (sub hj))
    (fun i hi j hj ne => overlap i (sub hi) j (sub hj) ne)
  have cap : (J.biUnion B).card ≤ C.card := by
    apply card_le_card
    intro x hx
    obtain ⟨i,hi,mem⟩ := mem_biUnion.mp hx
    exact contained i (sub hi) mem
  rw [size] at count
  omega

#print axioms representative_count
#print axioms bonferroni
end Erdos142RichBlocks
