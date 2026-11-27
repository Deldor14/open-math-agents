import OMAStatements.S_oeis_a054516
import Mathlib

/-! Expand the defining first-order recurrence at each higher index and
collect the resulting polynomial coefficients. -/
open OMA.S_oeis_a054516 in
theorem OMA.solution : type_of% @OMA.S_oeis_a054516.main := by
  intro k
  dsimp only
  simp only [fromThree,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  ring
