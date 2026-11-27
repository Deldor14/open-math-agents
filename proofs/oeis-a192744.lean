import OMAStatements.S_oeis_a192744
import Mathlib

open Polynomial OMA.S_oeis_a192744
namespace Deldor14.Poly192744

noncomputable abbrev M : ℤ[X] := X^2-X-1

theorem monicM : M.Monic := by
  change (X^2-X-1 : ℤ[X]).Monic
  rw [sub_sub]
  apply monic_X_pow_sub
  exact lt_of_le_of_lt (degree_add_le _ _) (by norm_num)

private abbrev f (n : ℕ) : ℤ := ((n.factorial : ℕ):ℤ)

private theorem degreeM : M.degree=2 := by
  unfold M
  rw [sub_sub,degree_sub_eq_left_of_degree_lt]
  · norm_num
  · exact lt_of_le_of_lt (degree_add_le _ _) (by norm_num)

private theorem xmod : (X : ℤ[X]) %ₘ M = X :=
  (modByMonic_eq_self_iff monicM).mpr (by rw [degreeM]; norm_num)
private theorem cmod (v : ℤ) : (C v : ℤ[X]) %ₘ M = C v :=
  (modByMonic_eq_self_iff monicM).mpr (by rw [degreeM]; exact lt_of_le_of_lt degree_C_le (by norm_num))

private theorem diff (n : ℕ) :
    a (n+2)-a (n+1)-a n=f (n+2)-f (n+1) := by
  have relation : p (n+2)-p (n+1)-p n =
      M*p n + C (f (n+1))*X + C (f (n+2)-f (n+1)) := by
    rw [p.eq_2 (n+1),p.eq_2 n]
    simp only [M,f,map_sub,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
    ring
  have h := congrArg (fun q : ℤ[X] => (q %ₘ M).coeff 0) relation
  simp only [sub_modByMonic,add_modByMonic,self_mul_modByMonic monicM,zero_add,
    ← smul_eq_C_mul,smul_modByMonic,xmod,cmod,coeff_sub,coeff_add,coeff_smul,coeff_C,coeff_X,
    smul_eq_mul] at h
  simpa [a] using h

theorem result : type_of% @OMA.S_oeis_a192744.main := by
  constructor
  · intro n hn
    obtain ⟨k,rfl⟩ : ∃ k,n=k+4 := ⟨n-4,by omega⟩
    simp only [show k+4-1=k+3 by omega,show k+4-2=k+2 by omega,show k+4-3=k+1 by omega,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_ofNat]
    have h0 := diff k
    have h1 := diff (k+1)
    have h2 := diff (k+2)
    simp only [f,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at h0 h1 h2
    linear_combination h2 - ((k:ℤ)+5)*h1 + ((k:ℤ)+2)*h0
  · intro n hn
    obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
    simp only [show k+3-1=k+2 by omega,show k+3-2=k+1 by omega,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_ofNat]
    have h0 := diff k
    have h1 := diff (k+1)
    simp only [f,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at h0 h1
    linear_combination (-(k:ℤ)-1)*h1 + ((k:ℤ)+2)^2*h0
end Deldor14.Poly192744

theorem OMA.solution : type_of% @OMA.S_oeis_a192744.main := Deldor14.Poly192744.result
