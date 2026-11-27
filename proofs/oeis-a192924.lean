import OMAStatements.S_oeis_a192924
import Mathlib

open Polynomial OMA.S_oeis_a192924
namespace Deldor14.Poly192924

noncomputable abbrev M : ℤ[X] := X^2-X-1

private theorem monicM : M.Monic := by
  change (X^2-X-1 : ℤ[X]).Monic
  rw [sub_sub]
  apply monic_X_pow_sub
  exact lt_of_le_of_lt (degree_add_le _ _) (by norm_num)

private theorem relation (k : ℕ) :
    p (k+4) + C (2*(-((k:ℤ)+4)+1)) * p (k+3) +
    C (((k:ℤ)+4)^2-3*((k:ℤ)+4)-1) * p (k+2) +
    C (3*(((k:ℤ)+4)-2)) * p (k+1) + p k =
      M*((X^2+X-1)*p k) := by
  rw [p.eq_3 (k+2),p.eq_3 (k+1),p.eq_3 k]
  simp only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,map_sub,map_add,map_mul,map_pow,
    map_natCast,map_ofNat,map_one,map_neg,M]
  ring

theorem result (n : ℕ) (hn : 4≤n) :
    a n + 2*(-(n:ℤ)+1)*a (n-1) + ((n:ℤ)^2-3*n-1)*a (n-2) +
      3*((n:ℤ)-2)*a (n-3)+a (n-4)=0 := by
  obtain ⟨k,rfl⟩ : ∃ k, n=k+4 := ⟨n-4, by omega⟩
  have h := congrArg (fun f : ℤ[X] => (f %ₘ M).coeff 0) (relation k)
  simp only [add_modByMonic,← smul_eq_C_mul,smul_modByMonic,coeff_add,coeff_smul,
    smul_eq_mul,self_mul_modByMonic monicM,coeff_zero] at h
  simpa only [a,Nat.cast_add,Nat.cast_ofNat,Nat.add_sub_cancel,
    show k+4-1=k+3 by omega,show k+4-2=k+2 by omega,show k+4-3=k+1 by omega] using h
end Deldor14.Poly192924

theorem OMA.solution : type_of% @OMA.S_oeis_a192924.main := Deldor14.Poly192924.result
