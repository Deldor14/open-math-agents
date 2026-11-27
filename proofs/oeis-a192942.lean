import OMAStatements.S_oeis_a192942
import Mathlib

open Polynomial OMA.S_oeis_a192942

namespace Deldor14.Product192942

noncomputable abbrev M : ℤ[X] := X^2-X-1

theorem monicM : M.Monic := by
  change (X^2-X-1 : ℤ[X]).Monic
  rw [sub_sub]
  apply monic_X_pow_sub
  exact lt_of_le_of_lt (degree_add_le _ _) (by norm_num)

theorem step (k : ℕ) : p (k+1) = p k * (C 2 * X + C ((k:ℤ)+1)) := by
  unfold p
  rw [Finset.prod_Icc_succ_top (by omega),Nat.cast_succ]

theorem relation (k : ℕ) :
    p (k+2) + C (-2*((k:ℤ)+2)-1) * p (k+1) + C (((k:ℤ)+2)^2-5) * p k =
      M * (4 * p k) := by
  rw [step (k+1),step k]
  simp only [Nat.cast_succ, map_sub, map_add, map_mul, map_pow, map_natCast,
    map_ofNat, map_one, map_neg, M]
  ring

end Deldor14.Product192942
open Deldor14.Product192942

theorem OMA.solution : type_of% @OMA.S_oeis_a192942.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
  have h := congrArg (fun f : ℤ[X] => (f %ₘ M).coeff 1) (relation k)
  simp only [add_modByMonic, ← smul_eq_C_mul, smul_modByMonic, coeff_add, coeff_smul,
    smul_eq_mul, self_mul_modByMonic monicM, coeff_zero] at h
  simpa only [a,Nat.cast_add,Nat.cast_ofNat,Nat.add_sub_cancel,
    show k+2-1=k+1 by omega] using h
