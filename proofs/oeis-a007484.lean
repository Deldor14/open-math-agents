import OMAStatements.S_oeis_a007484
import Mathlib

open OMA.S_oeis_a007484

/-- The two sides satisfy the same recurrence and agree on the initial pair. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a007484.main := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h k =>
    change 8*(3*a (n+1)+2*a n)=3*b (n+3)+2*b (n+2)+(3*c (n+2)+2*c (n+1))
    change 8*a (n+1)=b (n+3)+c (n+2) at k
    omega
