import RothRecordNineteen

open Finset
namespace Erdos142FutureRecords

/-- Search in the first n sites with some larger sites already selected. -/
private def can : ℕ → Finset ℕ → ℕ → Bool
  | 0, _, k => k==0
  | n+1, B, k =>
    if k=0 then true else if n+1<k then false else
    can n B k || (decide (∀ y ∈ B, ∀ z ∈ B, n+z=y+y → n=z) && can n (insert n B) (k-1))

private theorem covers_search (A : Finset ℕ) (free : ThreeAPFree (↑A : Set ℕ))
    (n : ℕ) (B : Finset ℕ) (k : ℕ) (inc : B ⊆ A) (many : k≤((range n) ∩ A).card) :
    can n B k=true := by
  induction n generalizing B k with
  | zero => simp at many; simp [can,many]
  | succ n ih =>
    have cap := card_le_card (inter_subset_left (s₁:=range (n+1)) (s₂:=A))
    rw [card_range] at cap
    have nk : ¬n+1<k := by omega
    by_cases zero : k=0
    · simp [can,zero]
    simp only [can,if_neg zero,if_neg nk,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    rw [range_add_one] at many
    by_cases inside : n ∈ A
    · right
      refine ⟨fun y hy z hz e => threeAPFree_iff_eq_right.mp free inside (inc hy) (inc hz) e,?_⟩
      apply ih (insert n B) (k-1) (insert_subset inside inc)
      rw [insert_inter_of_mem inside,card_insert_of_notMem (by simp)] at many
      omega
    · left
      apply ih B k inc
      simpa [insert_inter_of_notMem inside] using many

set_option maxRecDepth 32000 in
set_option maxHeartbeats 8000000 in
private theorem enumerated : can 19 ∅ 9=false := by decide

private theorem from_square (x : ℕ) (lo : 64*19≤19*x^2) : 8≤x := by
  by_contra! small
  have sq := Nat.pow_le_pow_left (show x≤7 by omega) 2
  norm_num at sq lo
  omega

theorem at_nineteen : rothNumberNat 19=8 := by
  obtain ⟨A,fit,sz,free⟩ := rothNumberNat_spec 19
  have lo := beyond_nineteen 19 le_rfl
  have up : rothNumberNat 19<9 := by
    by_contra! large
    have card : 9≤((range 19) ∩ A).card := by rwa [inter_eq_right.mpr fit,sz]
    have e := covers_search A free 19 ∅ 9 (empty_subset _) card
    rw [enumerated] at e
    exact Bool.false_ne_true e
  exact Nat.le_antisymm (Nat.le_of_lt_succ up) (from_square _ lo)

theorem record_nineteen : record 19 := by
  intro m hm
  apply (square_iff (by decide : 0<19) (show 0<m by omega)).mpr
  simpa [PowerLE,at_nineteen,Nat.mul_comm] using beyond_nineteen m hm

#print axioms at_nineteen
#print axioms record_nineteen
end Erdos142FutureRecords
