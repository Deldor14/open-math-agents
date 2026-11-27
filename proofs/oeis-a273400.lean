import OMAStatements.S_oeis_a273400
import Mathlib

namespace Deldor14.IteratedCatalan
open OMA.S_oeis_a273400 Finset

private theorem doubling (n : ℕ) (hn : 0 < n) : 2*catalan n ≤ catalan (n+1) := by
  rw [catalan_succ']
  have h : ({(0,n),(n,0)} : Finset (ℕ×ℕ)) ⊆ antidiagonal n := by
    intro p hp
    simp only [mem_insert,mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp
  have ne : (0,n) ≠ (n,0) := by intro he; have := congrArg Prod.fst he; simp at this; omega
  have le := sum_le_sum_of_subset_of_nonneg (f:=fun p : ℕ×ℕ => catalan p.1*catalan p.2) h (by intros; omega)
  simpa [ne,two_mul] using le
private theorem expLower (k : ℕ) : 2^k ≤ catalan (k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := doubling (k+1) (by omega)
    rw [pow_succ]
    omega
private theorem linearLower (k : ℕ) (hk : 7 ≤ k) : 4*k+1 ≤ catalan k := by
  induction k,hk using Nat.le_induction with
  | base =>
    have h := expLower 6
    norm_num at h ⊢
    omega
  | succ k hk ih =>
    have e := doubling k (by omega)
    omega
theorem result : type_of% @OMA.S_oeis_a273400.main := by
  apply (Set.finite_lt_nat 7).subset
  intro n h
  change n < 7
  by_contra! hn
  have kn : 7 ≤ catalan n := by have := linearLower n hn; omega
  let k := catalan n
  have big : 4*k+1 ≤ catalan k := linearLower k kn
  obtain ⟨r,hr⟩ : ∃ r, catalan k = r+1 := ⟨catalan k-1,by omega⟩
  have high : 10^k ≤ catalan (catalan k) := calc
    10^k ≤ (2^4)^k := Nat.pow_le_pow_left (by decide) _
    _ = 2^(4*k) := (pow_mul 2 4 k).symm
    _ ≤ 2^r := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ catalan (catalan k) := hr ▸ expLower r
  have lt := Nat.lt_base_pow_length_digits (m:=a n) (by decide : 1<10)
  have bad : (Nat.digits 10 (a n)).length < k := h
  have hh := Nat.pow_le_pow_right (by decide : 0<10) bad.le
  change 10^k ≤ a n at high
  omega

end Deldor14.IteratedCatalan
theorem OMA.solution : type_of% @OMA.S_oeis_a273400.main := Deldor14.IteratedCatalan.result
