import OMAStatements.S_oeis_a005517
import Mathlib

open PowerSeries OMA.S_oeis_a005517

theorem Deldor14.matulaStep (n : ℕ) (h : 3≤n) : A005517 (n+3)=5*A005517 n := by
  unfold A005517
  have h3 : (n+3)%3=n%3 := by omega
  rw [h3]
  simp only [if_neg (show n+3≠0 by omega),if_neg (show n+3≠1 by omega),
    if_neg (show n+3≠2 by omega),if_neg (show n≠0 by omega),if_neg (show n≠1 by omega),
    if_neg (show n≠2 by omega)]
  split_ifs
  all_goals first
    | rw [show (n+3-3)/3=(n-3)/3+1 by omega,pow_succ]; ring
    | rw [show (n+3-1)/3=(n-1)/3+1 by omega,pow_succ]; ring
    | rw [show (n+3-5)/3=(n-5)/3+1 by omega,pow_succ]; ring

theorem OMA.solution : type_of% @OMA.S_oeis_a005517.main := by
  let s : PowerSeries ℚ := mk fun n => (A005517 (n+1):ℚ)
  change s * _ = _
  have eqn : s*(1-5*X^3)=s-(C (5:ℚ)*s)*X^3 := by rw [map_ofNat]; ring
  rw [eqn]
  apply PowerSeries.ext
  intro n
  have two : 2*(X:PowerSeries ℚ)=C (2:ℚ)*X^1 := by rw [map_ofNat,pow_one]
  have three : 3*(X:PowerSeries ℚ)^2=C (3:ℚ)*X^2 := by rw [map_ofNat]
  rw [two,three]
  simp only [map_sub,map_add,coeff_C_mul_X_pow,coeff_mul_X_pow',coeff_C_mul,coeff_one,
    coeff_X_pow,s,coeff_mk]
  by_cases small : n≤4
  · interval_cases n <;> norm_num [A005517]
  · have shift := Deldor14.matulaStep (n-3+1) (by omega)
    rw [show n-3+1+3=n+1 by omega] at shift
    simp [show 3≤n by omega,show n≠4 by omega,show n≠2 by omega,
      show n≠1 by omega,show n≠0 by omega,show 1≤n by omega,show 2≤n by omega,
      show n-1≠0 by omega,show n-2≠0 by omega,coeff_C,shift]
