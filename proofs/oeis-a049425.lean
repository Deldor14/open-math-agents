import OMAStatements.S_oeis_a049425
import Mathlib

open PowerSeries OMA.S_oeis_a049425

/-- The chain rule for the exponential generating function in Munarini's proof. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a049425.main := by
  intro n
  have hs : HasSubst parameter := HasSubst.of_constantCoeff_zero' (by simp [parameter])
  have three : (C (1/3:ℚ) : PowerSeries ℚ)*3 = 1 := by
    calc _ = C ((1/3:ℚ)*3) := by rw [map_mul,map_ofNat]
         _ = 1 := by norm_num
  have delta : derivative ℚ parameter = 1 + 2*X + X^2 := by
    unfold parameter
    simp only [map_add, derivative_pow, derivative_X, Derivation.leibniz,
      derivative_C, smul_eq_mul, mul_zero, add_zero, Nat.cast_ofNat,
      Nat.reduceSub, pow_one, mul_one]
    linear_combination X^2 * three
  have eqn : derivative ℚ series = series + (series*X + series*X) + series*X^2 := by
    calc _ = series*derivative ℚ parameter := by
           unfold series
           rw [derivative_subst hs,derivative_exp]
         _ = _ := by rw [delta]; ring
  have h := congrArg (coeff (n+2)) eqn
  simp only [coeff_derivative, map_add, coeff_succ_mul_X, coeff_mul_X_pow, Nat.cast_add, Nat.cast_ofNat] at h
  unfold a
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
  linear_combination ((n:ℚ)+2)*((n:ℚ)+1)*(n.factorial:ℚ)*h
