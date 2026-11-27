import OMAStatements.S_oeis_a192473
import Mathlib

open Polynomial OMA.S_oeis_a192473

namespace Deldor14.QuadraticPowers

noncomputable abbrev M : ℤ[X] := X^2-X-1
noncomputable def factor (k : ℕ) : ℤ[X] :=
  (X^2-3*X+1)*X^k + (X^4-X^2-1)*(X^2+X-1)*X^(2*k+2)

theorem relation (k : ℕ) :
    p (k+4) + C 3*p (k+2) + C 2*p (k+1) =
    M*factor k + 1 + C 4*p (k+3) + p k := by
  unfold p M factor
  rw [show 2*(k+4)+2 = (2*k+2)+8 by omega,
      show 2*(k+3)+2 = (2*k+2)+6 by omega,
      show 2*(k+2)+2 = (2*k+2)+4 by omega,
      show 2*(k+1)+2 = (2*k+2)+2 by omega]
  simp only [pow_add,map_ofNat]
  ring

end Deldor14.QuadraticPowers
open Deldor14.QuadraticPowers

theorem OMA.solution : type_of% @OMA.S_oeis_a192473.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k, n=k+4 := ⟨n-4,by omega⟩
  have mon : M.Monic := by unfold M; monicity!
  have deg : M.degree = 2 := by unfold M; compute_degree!
  have one : (1:ℤ[X]) %ₘ M=1 :=
    (modByMonic_eq_self_iff mon).mpr (by rw [degree_one,deg]; decide)
  have h := congrArg (fun f : ℤ[X] => (f %ₘ M).coeff 1) (relation k)
  simp only [add_modByMonic, ← smul_eq_C_mul, smul_modByMonic, coeff_add, coeff_smul,
    smul_eq_mul, self_mul_modByMonic mon, coeff_zero, one,coeff_one,if_neg (by decide : (1:ℕ) ≠ 0)] at h
  simp only [a,show k+4-1=k+3 by omega,show k+4-2=k+2 by omega,
    show k+4-3=k+1 by omega,Nat.add_sub_cancel]
  linarith
