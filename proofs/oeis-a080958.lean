import OMAStatements.S_oeis_a080958
import Mathlib

open OMA.S_oeis_a080958
namespace Deldor14.AlternatingFactorials

private theorem step (k : ℕ) : a (k+1) =
    ((k:ℚ)+1)*a k + (k.factorial:ℚ)*(-1)^(k+2)*((k:ℚ)+2) := by
  unfold a
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1),Nat.factorial_succ]
  push_cast
  have ne : (k:ℚ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem result : type_of% @OMA.S_oeis_a080958.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+1 := ⟨n-1,by omega⟩
  rw [Nat.add_sub_cancel,step (k+1),step k,Nat.factorial_succ]
  push_cast
  simp only [pow_succ]
  ring
end Deldor14.AlternatingFactorials

theorem OMA.solution : type_of% @OMA.S_oeis_a080958.main := Deldor14.AlternatingFactorials.result
