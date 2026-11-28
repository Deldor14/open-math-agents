import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

open Finset
namespace Erdos142Entropy

/-- Distinct prime divisors consume at least one binary digit each. -/
theorem prime_multiplicity (d : ℕ) (hd : 0 < d) :
    d.primeFactors.card ≤ Nat.log 2 d := by
  apply Nat.le_log_of_pow_le (by decide : 1 < 2)
  calc
    2 ^ d.primeFactors.card = ∏ _p ∈ d.primeFactors, (2 : ℕ) := by simp
    _ ≤ ∏ p ∈ d.primeFactors, p := prod_le_prod' (fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ d := Nat.le_of_dvd hd (Nat.prod_primeFactors_dvd d)

/-- A pair in every surviving cover edge supplies a nonzero difference. The
    per-prime excesses may therefore be summed with controlled multiplicity. -/
theorem excess_sum {α : Type*} (P : Finset ℕ) (E : Finset α) (n : ℕ)
    (gap : α → ℕ) (deficit : ℕ → ℕ)
    (hgap : ∀ e ∈ E, 0 < gap e ∧ gap e ≤ n)
    (localBound : ∀ p ∈ P, deficit p ≤ ∑ e ∈ E,
      if p ∈ (gap e).primeFactors then 1 else 0) :
    ∑ p ∈ P, deficit p ≤ E.card * Nat.log 2 n := by
  classical
  calc
    _ ≤ ∑ p ∈ P, ∑ e ∈ E, if p ∈ (gap e).primeFactors then 1 else 0 :=
      sum_le_sum localBound
    _ = ∑ e ∈ E, ∑ p ∈ P, if p ∈ (gap e).primeFactors then 1 else 0 := sum_comm
    _ ≤ ∑ _e ∈ E, Nat.log 2 n := by
      apply sum_le_sum
      intro e he
      have hsub : P.filter (fun p => p ∈ (gap e).primeFactors) ⊆ (gap e).primeFactors :=
        fun p hp => (mem_filter.mp hp).2
      have hh := (card_le_card hsub).trans (prime_multiplicity (gap e) (hgap e he).1)
      have hl := hh.trans (Nat.log_mono_right (hgap e he).2)
      simpa using hl
    _ = _ := by simp

#print axioms prime_multiplicity
#print axioms excess_sum
end Erdos142Entropy
