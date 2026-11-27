import OMAStatements.S_oeis_a383702
import Mathlib

open Polynomial OMA.S_oeis_a383702
namespace Deldor14.Words383702

private theorem step (n : ℕ) : row (n+1) = row n*(X+C (4*(n:ℤ)+3)) := by
  simp [row,Finset.prod_range_succ]

private theorem relation (k : ℕ) :
    row (k+3)+C (3*(-4*((k:ℤ)+3)+5))*row (k+2)+
    C (48*((k:ℤ)+3)^2-168*((k:ℤ)+3)+151)*row (k+1)-
    C ((4*((k:ℤ)+3)-9)^3)*row k = row k * X^3 := by
  rw [step (k+2),step (k+1),step k]
  simp only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,map_add,map_sub,map_pow,map_mul,
    map_ofNat,map_neg,map_natCast,map_one]
  ring

theorem result : type_of% @OMA.S_oeis_a383702.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
  have h := congrArg (fun q : ℤ[X] => q.coeff 2) (relation k)
  simp only [coeff_sub,coeff_add,coeff_C_mul,coeff_mul_X_pow'] at h
  simpa [a,show k+3-1=k+2 by omega,show k+3-2=k+1 by omega] using h
end Deldor14.Words383702

theorem OMA.solution : type_of% @OMA.S_oeis_a383702.main := Deldor14.Words383702.result
