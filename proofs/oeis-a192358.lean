import OMAStatements.S_oeis_a192358
import Mathlib

namespace Deldor14.QuadraticReduction
open OMA.S_oeis_a192358 Polynomial

theorem result : type_of% @OMA.S_oeis_a192358.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+5 := ⟨n-5,by omega⟩
  let d : ℚ[X] := X^2-X-1
  let diff := p (k+4)-(2:ℚ) • p (k+3)-(19:ℚ) • p (k+2)+(20:ℚ) • p (k+1)+(55:ℚ) • p k
  have factor : d ∣ diff := by
    refine ⟨C (1/2)*((X+C 3)^k*((X+C 3)^2+5*(X+C 3)+5)+(X-C 3)^k*((X-C 3)^2-7*(X-C 3)+11)),?_⟩
    simp only [diff,p,d,smul_eq_C_mul,pow_add,map_ofNat]
    ring
  have mon : d.Monic := by
    dsimp [d]
    rw [sub_sub]
    apply monic_X_pow_sub
    exact (degree_add_le ..).trans_lt (by norm_num)
  have eq := (mem_ker_modByMonic mon).mpr factor
  rw [LinearMap.mem_ker] at eq
  have h := congrArg (fun f : ℚ[X] => f.coeff 1) eq
  simp only [diff,map_add,map_sub,map_smul,coeff_add,coeff_sub,coeff_smul,coeff_zero,smul_eq_mul,modByMonicHom_apply] at h
  unfold a
  simp only [show k+5-1=k+4 by omega,show k+4-1=k+3 by omega,show k+5-2=k+3 by omega,
    show k+3-1=k+2 by omega,show k+5-3=k+2 by omega,show k+2-1=k+1 by omega,
    show k+5-4=k+1 by omega,Nat.add_sub_cancel]
  dsimp [d] at h
  linarith
end Deldor14.QuadraticReduction
theorem OMA.solution : type_of% @OMA.S_oeis_a192358.main := Deldor14.QuadraticReduction.result
