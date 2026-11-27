import OMAStatements.S_oeis_a134119
import Mathlib

open PowerSeries OMA.S_oeis_a134119

private theorem ten_shift (n : ℕ) : a (n+10) = a n + 2 := by
  have p : ((n:ℚ)+10)^2 / 10 = (n:ℚ)^2 / 10 + ((2*(n:ℤ)+10:ℤ):ℚ) := by push_cast; ring
  have q : ((n:ℚ)+10-1)^2 / 10 = ((n:ℚ)-1)^2 / 10 + ((2*(n:ℤ)+8:ℤ):ℚ) := by push_cast; ring
  simp only [a, Nat.cast_add, Nat.cast_ofNat, p, q, Int.floor_add_intCast]
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a134119.main := by
  have numerator : (X : PowerSeries ℤ)^4 * (X^4 + 1) = X^8 + X^4 := by ring
  rw [numerator, mul_add, mul_sub, mul_sub, mul_one]
  apply PowerSeries.ext
  intro n
  have oneShift (p : PowerSeries ℤ) : coeff n (p * X) =
      (if 1 ≤ n then coeff (n-1) p else 0) := by simpa using coeff_mul_X_pow' p 1 n
  simp only [map_add, map_sub, coeff_mul_X_pow', oneShift, coeff_X_pow, coeff_mk]
  by_cases small : n ≤ 10
  · interval_cases n <;> norm_num [a]
  · have h11 : 11 ≤ n := by omega
    have h10 : 10 ≤ n := by omega
    have h1 : 1 ≤ n := by omega
    have h8 : 8 ≠ n := by omega
    have h4 : 4 ≠ n := by omega
    have h8' : n ≠ 8 := Ne.symm h8
    have h4' : n ≠ 4 := Ne.symm h4
    simp [h11,h10,h1,h8,h4,h8',h4']
    have left := ten_shift (n-11)
    have right := ten_shift (n-10)
    rw [show n-11+10=n-1 by omega] at left
    rw [show n-10+10=n by omega] at right
    omega
