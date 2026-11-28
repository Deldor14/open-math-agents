import RothPrimeTransversals

open Finset
open Erdos142RowSelection Erdos142PrimeRows Erdos142LongDigits
namespace Erdos142RowExample

private def U : Finset ℕ :=
  {0,1,3,4,9,10,12,13,27,28,30,31,36,37,39,40,
   81,82,84,85,90,91,93,94,108,109,111,112,117,118,120,121}

private def V : Finset ℕ := {0,1,3,4}

private theorem from_pairs (S : Finset ℕ) (ok : ∀ x ∈ S, ∀ y ∈ S, x<y → 2*y-x ∉ S) : Free 3 S := by
  intro x q pos hit
  have h0 := hit 0 (by decide)
  have h1 := hit 1 (by decide)
  have h2 := hit 2 (by decide)
  simp only [Nat.zero_mul,Nat.add_zero,Nat.one_mul] at h0 h1
  have e : 2*(x+q)-x=x+2*q := by omega
  exact ok x h0 (x+q) h1 (by omega) (e ▸ h2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem Ufree : Free 3 U := from_pairs U (by decide)

private theorem Vfree : Free 3 V := from_pairs V (by decide)

private def starts (q t : ℕ) := (range t).image (fun a => (a,q))
private def F := starts 1 1281 ∪ starts 3 771 ∪ starts 5 261
private def bad := (range 3) ∪ Icc 22 1536

private theorem sizeF : F.card≤2313 := by
  have ub (q t : ℕ) : (starts q t).card≤t := card_image_le.trans_eq (card_range t)
  have x := card_union_le (starts 1 1281) (starts 3 771)
  have y := card_union_le (starts 1 1281 ∪ starts 3 771) (starts 5 261)
  have a := ub 1 1281
  have b := ub 3 771
  have c := ub 5 261
  dsimp only [F]
  omega

private theorem family {a q : ℕ} : (a,q) ∈ F ↔
    (q=1 ∧ a<1281) ∨ (q=3 ∧ a<771) ∨ (q=5 ∧ a<261) := by
  simp [F,starts,and_comm,eq_comm]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem budget : 2313*badCount 32 12 4 bad<12^32 := by decide

set_option maxRecDepth 20000 in
theorem three_hits_on_odd_steps :
    ∃ A ⊆ range 1536, Set.IsAPOfLengthFree (↑A : Set ℕ) 3 ∧
      ∀ a q : ℕ, Odd q → a+255*q<1536 →
        3≤((progression 256 a q) ∩ A).card ∧ ((progression 256 a q) ∩ A).card≤21 := by
  have unit (f : ℕ×ℕ) (hf : f ∈ F) : f.2.Coprime 256 := by
    obtain ⟨a,q⟩ := f
    rcases family.mp hf with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;> dsimp only <;> decide
  have fit (f : ℕ×ℕ) (hf : f ∈ F) : progression 256 f.1 f.2 ⊆ range 1536 := by
    obtain ⟨a,q⟩ := f
    intro y hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
    have lim := mem_range.mp hi
    apply mem_range.mpr
    rcases family.mp hf with ⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩ <;> dsimp only <;> omega
  have uc : U.card=32 := by decide
  have vc : V.card=4 := by decide
  have cap : F.card*badCount U.card (2*6) V.card bad<(2*6)^U.card := by
    rw [uc,vc]
    exact (Nat.mul_le_mul_right _ sizeF).trans_lt budget
  obtain ⟨A,inc,free,test⟩ := progression_selection (k:=3) (p:=256) (T:=6) (n:=1536) (w:=128)
    (by decide) (by decide) (by decide) (by decide) U V (by decide) (by decide) Ufree Vfree F unit fit bad cap
  refine ⟨A,inc,free,?_⟩
  intro a q odd lim
  obtain ⟨j,hj⟩ := odd
  have f : (a,q) ∈ F := family.mpr (by omega)
  have h := test _ f
  have small := card_le_card ((inter_subset_right (s₁:=progression 256 a q) (s₂:=A)).trans inc)
  rw [card_range] at small
  simp only [bad,mem_union,mem_range,mem_Icc,not_or] at h
  omega

#print axioms three_hits_on_odd_steps
end Erdos142RowExample
