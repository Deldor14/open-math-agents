import OMAStatements.S_oeis_a137560
import Mathlib

/-! The coefficient of degree k is already stable in the kth iterate.
The two endpoint terms of its convolution vanish, leaving the Catalan recurrence. -/
namespace Deldor14.IteratedQuadratic
open Polynomial Finset OMA.S_oeis_a137560
private lemma constant_zero (n : ℕ) : (P n).coeff 0 = 0 := by
  induction n with
  | zero => simp [P]
  | succ n ih => simp [P,pow_two,coeff_mul,ih]

private theorem stable (n j : ℕ) (h : j + 1 ≤ n) :
    (P n).coeff (j + 1) = (catalan j : ℤ) := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    rw [P,coeff_add,pow_two,coeff_mul]
    cases j with
    | zero => simp [Finset.Nat.antidiagonal_succ, constant_zero]
    | succ j =>
      rw [Finset.Nat.sum_antidiagonal_succ]
      simp only [constant_zero,zero_mul,zero_add]
      rw [Finset.Nat.sum_antidiagonal_succ']
      simp only [constant_zero,mul_zero,zero_add]
      rw [coeff_X_of_ne_one (by omega),add_zero,catalan_succ']
      push_cast
      apply sum_congr rfl
      intro ij hij
      have eq := mem_antidiagonal.mp hij
      rw [ih ij.1 (by omega),ih ij.2 (by omega)]

theorem result : type_of% @OMA.S_oeis_a137560.main := by
  rintro (_|k) h
  · omega
  exact ⟨k+1,fun n hn => stable n k hn⟩
end Deldor14.IteratedQuadratic
theorem OMA.solution : type_of% @OMA.S_oeis_a137560.main := Deldor14.IteratedQuadratic.result
