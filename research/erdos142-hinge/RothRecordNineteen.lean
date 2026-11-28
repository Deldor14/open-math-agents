import RothPowerRecords

open Finset
namespace Erdos142FutureRecords

private def samples : List (ℕ × Finset ℕ) :=
  [(19,{0,1,3,4,9,10,12,13}),
   (20,{0,1,5,6,8,13,14,17,19}),
   (25,{0,1,3,9,10,13,14,21,22,24}),
   (30,{0,1,3,4,9,10,12,22,25,26,29}),
   (36,{0,1,3,4,9,10,12,13,27,28,30,31}),
   (43,{0,1,3,4,9,10,12,13,27,28,30,31,36}),
   (51,{0,1,3,4,9,10,12,13,27,28,30,31,36,37})]

private theorem fit : ∀ t ∈ samples, (∀ x ∈ t.2, x<t.1) ∧
    (∀ x ∈ t.2, ∀ y ∈ t.2, ∀ z ∈ t.2, x+z=y+y → x=z) := by decide

private theorem check : ∀ m ∈ range 57, 19≤m →
    ∃ t ∈ samples, t.1≤m ∧ 64*m≤19*t.2.card^2 := by decide

/-- Seven small explicit sets prove one numerical all-future lower bound. -/
theorem beyond_nineteen (m : ℕ) (large : 19≤m) : 64*m≤19*(rothNumberNat m)^2 := by
  obtain ⟨u,hu,cmp⟩ := finite_descent (n:=19) (by decide) m large
  obtain ⟨lo,hi⟩ := mem_Ico.mp hu
  obtain ⟨t,ht,tu,fig⟩ := check u (mem_range.mpr (by omega)) lo
  have free : ThreeAPFree (↑t.2 : Set ℕ) := threeAPFree_iff_eq_right.mpr (fit t ht).2
  have bound := (free.le_rothNumberNat t.2 (fit t ht).1 rfl).trans (rothNumberNat.monotone tu)
  have cmp' := (square_iff (show 0<u by omega) (show 0<m by omega)).mp cmp
  simp only [PowerLE,pow_one] at cmp'
  have b := Nat.mul_le_mul_left 19 (Nat.pow_le_pow_left bound 2)
  have g := Nat.mul_le_mul_left m (fig.trans b)
  have h := Nat.mul_le_mul_left 19 cmp'
  have cancel : u*(64*m)≤u*(19*(rothNumberNat m)^2) := by nlinarith only [g,h]
  exact Nat.le_of_mul_le_mul_left cancel (by omega)

#print axioms beyond_nineteen
end Erdos142FutureRecords
