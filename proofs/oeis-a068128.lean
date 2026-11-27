import OMAStatements.S_oeis_a068128
import Mathlib

namespace Deldor14.ZeroTriangle
open OMA.S_oeis_a068128

private theorem value_zero (l : List ℕ) (h : l.sum=0) : Nat.ofDigits 10 l=0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.sum_cons,Nat.add_eq_zero_iff] at h
    simp [Nat.ofDigits_cons,h.1,ih h.2]

theorem result : ¬ (type_of% @OMA.S_oeis_a068128.main) := by
  intro hall
  apply (hall 0)
  apply (Set.finite_singleton (0:ℕ)).subset
  intro t ht
  have hz : (Nat.digits 10 t).sum=0 := ht.2
  simpa only [Nat.ofDigits_digits,Set.mem_singleton_iff] using value_zero _ hz

end Deldor14.ZeroTriangle
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a068128.main) := Deldor14.ZeroTriangle.result
