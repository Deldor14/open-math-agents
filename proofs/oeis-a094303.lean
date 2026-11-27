import OMAStatements.S_oeis_a094303
import Mathlib

namespace Deldor14.Companion
open OMA.S_oeis_a094303

private theorem align (k : ℕ) : (state (k+1)).1=(companion (k+2)).2 ∧
    (state (k+1)).2=(companion (k+2)).1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    change ((state (k+1)).1*(state (k+1)).2 = (companion (k+2)).1*(companion (k+2)).2) ∧
      (state (k+1)).2+(state (k+1)).1 = (companion (k+2)).1+(companion (k+2)).2
    simp [ih.1,ih.2,Nat.mul_comm]

theorem result : type_of% @OMA.S_oeis_a094303.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
  change (state (k+1)).1=(companion (k+2)).1+(companion (k+2)).2-(companion (k+2)).1
  rw [(align k).1]
  omega

end Deldor14.Companion
theorem OMA.solution : type_of% @OMA.S_oeis_a094303.main := Deldor14.Companion.result
