import OMAStatements.S_oeis_a135499
import Mathlib

open OMA.S_oeis_a135499

private theorem alternating (xs : List ℕ) :
    Nat.ofDigits 10 xs + (digitSums xs).2 ≡ (digitSums xs).1 [MOD 11] := by
  induction xs with
  | nil => rfl
  | cons d xs ih =>
    simp only [Nat.ofDigits_cons,digitSums,Prod.fst,Prod.snd]
    unfold Nat.ModEq at *
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a135499.main := by
  rintro n ⟨_,e⟩
  have h := alternating (Nat.digits 10 n)
  rw [Nat.ofDigits_digits,e] at h
  unfold Nat.ModEq at h
  omega
