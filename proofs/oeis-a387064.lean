import OMAStatements.S_oeis_a387064
import Mathlib

open OMA.S_oeis_a387064 Finset

/-- The earlier rows cannot reach valuation k. In the final row the valuation
is k exactly in the columns coprime to p, giving Euler's totient. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a387064.main := by
  intro p k hp hk
  have large : 1 < p^k := one_lt_pow₀ hp.one_lt (by omega)
  have noOne : ¬ p^k ∣ 1 := by simpa using (by omega : p^k ≠ 1)
  have early (r : ℕ) (hr : r<p^k) :
      ((range (r+1)).filter (fun j => p^k ∣ r.choose j)).card=0 := by
    rw [card_eq_zero,filter_eq_empty_iff]
    intro j hj
    have hj' : j≤r := by simpa using hj
    by_cases zr : r=0
    · have zj : j=0 := by omega
      simpa [zr,zj] using noOne
    · rw [hp.pow_dvd_iff_le_factorization (Nat.choose_pos hj').ne']
      have ub : (r.choose j).factorization p ≤ Nat.log p r := Nat.factorization_choose_le_log
      have := (Nat.log_lt_iff_lt_pow hp.one_lt zr).mpr hr
      omega
  have last : (range (p^k+1)).filter (fun j => p^k ∣ (p^k).choose j) =
      (range (p^k)).filter (fun j => (p^k).Coprime j) := by
    ext j
    simp only [mem_filter,mem_range,Nat.coprime_pow_left_iff hk,hp.coprime_iff_not_dvd]
    by_cases h : j<p^k
    · simp only [h,h.le,Nat.lt_succ_of_le h.le,true_and]
      by_cases z : j=0
      · simpa [z] using noOne
      · rw [hp.pow_dvd_iff_le_factorization (Nat.choose_pos h.le).ne']
        have add := Nat.factorization_choose_prime_pow_add_factorization hp h.le z
        have iff : j.factorization p=0 ↔ ¬ p ∣ j := by
          simp [Nat.factorization_eq_zero_iff,hp,z]
        omega
    · by_cases e : j=p^k
      · simp [e,noOne]
      · simp [h,show ¬ j<p^k+1 by omega]
  rw [a,sum_range_succ,Finset.sum_eq_zero (fun r hr => early r (mem_range.mp hr)),zero_add,last,
    ← Nat.totient_eq_card_coprime,Nat.totient_prime_pow hp hk,mul_comm]
