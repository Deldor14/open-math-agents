import OMAStatements.S_oeis_a002449
import Mathlib

namespace Deldor14.NestedSums
open OMA.S_oeis_a002449 Finset
private lemma weights (n i : ℕ) : c (n+1) (2*i)=H n i := by
  induction n generalizing i with
  | zero => simp [c,H,Nat.card_Icc]
  | succ n ih =>
    change (∑ m ∈ Icc 1 (2*i), c (n+1) (2*m)) = ∑ t ∈ Icc 1 (2*i), H n t
    exact sum_congr rfl (fun x _ => ih x)
theorem full : type_of% @OMA.S_oeis_a002449.main := by
  intro n _
  simpa [a,c] using weights n 1
end Deldor14.NestedSums
theorem OMA.solution : type_of% @OMA.S_oeis_a002449.main := Deldor14.NestedSums.full
