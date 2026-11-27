import OMAStatements.S_oeis_a025754
import Mathlib

open OMA.S_oeis_a025754

theorem OMA.solution : type_of% @OMA.S_oeis_a025754.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k, n = k+1 := ⟨n-1,by omega⟩
  have h := Ring.choose_smul_choose (1/9 : ℚ) (n:=k+1) (k:=k) (by omega)
  simp only [Nat.choose_succ_self_right, nsmul_eq_mul, Nat.cast_succ,
    Nat.add_sub_cancel_left, Nat.add_sub_cancel, Ring.choose_one_right] at h
  simp only [a, if_neg (by omega : k+1 ≠ 0), Nat.add_one_sub_one,
    if_neg (by omega : k ≠ 0), Nat.cast_succ, pow_succ]
  linear_combination 9 * (-81:ℚ)^k * h
