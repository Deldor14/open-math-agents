import Mathlib

namespace SquareFifth

/-- The part of Mulholland's Theorem 5.1, Table 5.1 (beta = 0, sign +)
    in which the abscissa is negative and the ordinate is positive. -/
def TableInput : Prop :=
  ∀ (j : ℕ) (X Y : ℚ), j < 10 → X < 0 → 0 < Y →
    Y ^ 2 = X ^ 5 + 2 ^ j → j = 1 ∧ X = -1 ∧ Y = 1

theorem classify (table : TableInput) (u d k : ℕ) (hu : 0 < u) (hd : 0 < d) :
    u ^ 2 + d ^ 5 = 2 ^ k ↔
      ∃ t : ℕ, k = 10 * t + 1 ∧ u = 2 ^ (5*t) ∧ d = 2 ^ (2*t) := by
  constructor
  · intro h
    let t := k / 10
    let j := k % 10
    have hk : k = 10*t+j := by dsimp [t,j]; omega
    let q : ℚ := 2 ^ t
    have hq : 0 < q := by dsimp [q]; positivity
    have hscaled : (u:ℚ)^2 + (d:ℚ)^5 = q^10 * (2:ℚ)^j := by
      calc
        _ = (2:ℚ)^k := by exact_mod_cast h
        _ = _ := by rw [hk, pow_add, Nat.mul_comm 10 t, pow_mul]
    let X : ℚ := -(d:ℚ) / q^2
    let Y : ℚ := (u:ℚ) / q^5
    have hx : X < 0 := by dsimp [X]; exact div_neg_of_neg_of_pos (by exact neg_lt_zero.mpr (by exact_mod_cast hd)) (by positivity)
    have hy : 0 < Y := by dsimp [Y]; positivity
    have hcurve : Y^2 = X^5 + 2^j := by
      dsimp [Y,X]
      field_simp [ne_of_gt hq]
      linear_combination hscaled
    obtain ⟨hj, hX, hY⟩ := table j X Y (Nat.mod_lt k (by decide)) hx hy hcurve
    have huq : (u:ℚ) = q^5 := by
      have := (div_eq_iff (by positivity : q^5 ≠ 0)).mp hY
      simpa using this
    have hdq : (d:ℚ) = q^2 := by
      have := (div_eq_iff (by positivity : q^2 ≠ 0)).mp hX
      linarith
    refine ⟨t, by omega, ?_, ?_⟩
    · rw [Nat.mul_comm 5 t, pow_mul]
      dsimp [q] at huq
      exact_mod_cast huq
    · rw [Nat.mul_comm 2 t, pow_mul]
      dsimp [q] at hdq
      exact_mod_cast hdq
  · rintro ⟨t, rfl, rfl, rfl⟩
    rw [← pow_mul, ← pow_mul, pow_add]
    have h₁ : 5*t*2 = 10*t := by omega
    have h₂ : 2*t*5 = 10*t := by omega
    rw [h₁,h₂]
    ring

theorem odd_base (table : TableInput) {u d k : ℕ} (hu : 0 < u)
    (hd : 1 < d) (odd : d % 2 = 1) : u^2 + d^5 ≠ 2^k := by
  intro h
  obtain ⟨t, _, _, hd'⟩ := (classify table u d k hu (by omega)).mp h
  cases t with
  | zero => simp_all
  | succ t =>
    rw [hd', Nat.mul_succ, pow_add] at odd
    omega

end SquareFifth
