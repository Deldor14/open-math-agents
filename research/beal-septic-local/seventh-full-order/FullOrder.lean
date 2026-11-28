import Mathlib.Tactic

namespace SepticFullOrder

/-- The prime-power size check beyond the three small totients. -/
theorem prime_power_growth (n f : ℕ) (hn : n^2 ≤ 2^f) (hf : 18 ≤ f) :
    (6*n)^6 < 29^f := by
  have h₁ : n^6 ≤ 2^(3*f) := by
    calc n^6 = (n^2)^3 := by ring
         _ ≤ (2^f)^3 := Nat.pow_le_pow_left hn 3
         _ = 2^(3*f) := by rw [← pow_mul]; congr 1; omega
  have h₂ : 6^6 < 2^f := lt_of_lt_of_le (by decide : 6^6 < 2^18)
    (Nat.pow_le_pow_right (by decide) hf)
  calc (6*n)^6 = 6^6 * n^6 := mul_pow _ _ _
       _ ≤ 6^6 * 2^(3*f) := Nat.mul_le_mul_left _ h₁
       _ < 2^f * 2^(3*f) := Nat.mul_lt_mul_of_pos_right h₂ (by positivity)
       _ = 16^f := by rw [← pow_add, show f+3*f=4*f by omega, pow_mul]; rfl
       _ ≤ 29^f := Nat.pow_le_pow_left (by decide) _

theorem small_prime_growth :
    (6*11)^6 < 29^10 ∧ (6*13)^6 < 29^12 ∧ (6*17)^6 < 29^16 := by decide

/-- Uniform counting bound in terms of the number of distinct primes. -/
theorem factor_count (t : ℕ) (ht : 2 ≤ t) : t*(2^t+1) ≤ 10^(t-1) := by
  induction t, ht using Nat.le_induction with
  | base => decide
  | succ t ht ih =>
    have h₁ : t+1 ≤ 2*t := by omega
    have h₂ : 2^(t+1)+1 ≤ 2*(2^t+1) := by rw [pow_succ]; omega
    have h := Nat.mul_le_mul h₁ h₂
    calc (t+1)*(2^(t+1)+1) ≤ (2*t)*(2*(2^t+1)) := h
         _ = 4*(t*(2^t+1)) := by ring
         _ ≤ 4*10^(t-1) := Nat.mul_le_mul_left 4 ih
         _ ≤ 10^((t+1)-1) := by
            rw [show (t+1)-1=(t-1)+1 by omega, pow_succ]; omega

end SepticFullOrder
