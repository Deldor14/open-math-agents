import OMAStatements.S_oeis_a192255
import Mathlib

/-! Modulo X²−X−1, the linear coefficients of the powers of X satisfy
the Fibonacci recurrence. Linearity then evaluates the defining polynomial. -/
namespace Deldor14.WeightedFibonacci
open Polynomial Finset OMA.S_oeis_a192255
private noncomputable abbrev M : ℤ[X] := X^2-X-1
private noncomputable def lin (f : ℤ[X]) : ℤ := (f %ₘ M).coeff 1
private lemma mon : M.Monic := by unfold M; monicity!
private lemma deg : M.degree=2 := by unfold M;compute_degree!
private lemma low₀ : lin 1=0 := by
  rw [lin,(modByMonic_eq_self_iff mon).mpr (by rw [degree_one,deg];decide)]
  simp only [coeff_one,if_neg (by decide : (1:ℕ) ≠ 0)]
private lemma low₁ : lin X=1 := by
  rw [lin,(modByMonic_eq_self_iff mon).mpr (by rw [degree_X,deg];decide)]
  simp
private lemma fibpow (n : ℕ) : lin (X^n)=(Nat.fib n:ℤ) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using low₀
  | one => simpa using low₁
  | more n ih jh =>
    have e : (X:ℤ[X])^(n+2) = M*X^n + (X^(n+1)+X^n) := by unfold M;rw [pow_add,pow_succ];ring
    have h:=congrArg lin e
    simp only [lin,add_modByMonic,coeff_add,self_mul_modByMonic mon,coeff_zero,zero_add] at h
    change lin (X^(n+2)) = lin (X^(n+1))+lin (X^n) at h
    rw [h,ih,jh,Nat.fib_add_two,Nat.cast_add];ring
theorem result : type_of% @OMA.S_oeis_a192255.main := by
  intro n
  simp only [a,Nat.add_sub_cancel]
  change lin (p n)=_
  induction n with
  | zero => simp [p,low₀]
  | succ n ih =>
    rw [p,Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1+1)]
    have e : ∀ (u v : ℤ[X]) (b : ℤ), lin (u + v*C b)=lin u+b*lin v := by
      intro u v b
      rw [mul_comm v,← smul_eq_C_mul]
      simp only [lin,add_modByMonic,smul_modByMonic,coeff_add,coeff_smul,smul_eq_mul]
    rw [e,ih,fibpow]
    simp only [Nat.add_sub_cancel,Nat.cast_succ]
    ring
end Deldor14.WeightedFibonacci
theorem OMA.solution : type_of% @OMA.S_oeis_a192255.main := Deldor14.WeightedFibonacci.result
