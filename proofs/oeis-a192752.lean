import OMAStatements.S_oeis_a192752
import Mathlib

open Polynomial OMA.S_oeis_a192752
namespace Deldor14.Poly192752

noncomputable abbrev M : ℤ[X] := X^2-X-1

theorem monicM : M.Monic := by
  change (X^2-X-1 : ℤ[X]).Monic
  rw [sub_sub]
  apply monic_X_pow_sub
  exact lt_of_le_of_lt (degree_add_le _ _) (by norm_num)

private abbrev f (n : ℕ) : ℤ := 4*(n:ℤ)+3

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

theorem result : type_of% @OMA.S_oeis_a192752.main := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    change ((C 1 : ℤ[X]) %ₘ M).coeff 0 = _
    rw [cmod]; norm_num [Nat.fib]
  | one =>
    change (((X*1+C 7 : ℤ[X]) %ₘ M).coeff 0) = _
    rw [mul_one,add_modByMonic,xmod,cmod]
    norm_num [Nat.fib,coeff_X,coeff_C]
  | more n ih jh =>
    have h := diff n
    simp only [f,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at h
    have f₁ := Nat.fib_add_two (n := n+1)
    have f₂ := Nat.fib_add_two (n := n+2)
    have f₃ := Nat.fib_add_two (n := n+3)
    zify at f₁ f₂ f₃
    linarith

end Deldor14.Poly192752

theorem OMA.solution : type_of% @OMA.S_oeis_a192752.main := Deldor14.Poly192752.result
