import FinitePrefix

/-! Self-products of the ceiling-linear extension and an overlap bound for
the sparse schedule. Both statements are abstract. The product inequality
for the underlying sequence is an input. -/

namespace Erdos142SelfProduct
open Erdos142FinitePrefix

theorem prefix_product {R : ℕ → ℕ} {p m n : ℕ} (hp : 0 < p) (hm : 0 < m)
    (positive : ∀ t, 0 < t → 0 < R t) (size : ∀ t, R t ≤ t)
    (original : R m * R n ≤ R ((2*m-1)*n)) :
    B R p m * B R p n ≤ B R p ((2*m-1)*n) := by
  by_cases fixed : B R p m = R m
  · rw [fixed]
    exact digits hp hm positive (size m) original
  have pm : p < m := by
    by_contra! short
    exact fixed (agrees_on_prefix hp positive short)
  have line : B R p m=m ⌈/⌉ p := max_eq_right (by
    by_contra! smaller
    exact fixed (max_eq_left smaller.le))
  have cap : p*(m ⌈/⌉ p) ≤ 2*m-1 := by
    rw [Nat.ceilDiv_eq_add_pred_div,Nat.mul_comm]
    have h := Nat.div_mul_le_self (m+p-1) p
    omega
  have ncap : B R p n ≤ n := max_le (size n) ((ceilDiv_le_iff_le_mul hp).mpr (by
    simpa using Nat.mul_le_mul_right n (show 1 ≤ p by omega)))
  let target := (2*m-1)*n
  have cover : target ≤ p*(target ⌈/⌉ p) := (ceilDiv_le_iff_le_mul hp).mp le_rfl
  rw [line]
  apply le_trans _ (le_max_right _ _)
  apply Nat.le_of_mul_le_mul_left _ hp
  rw [← Nat.mul_assoc]
  exact (Nat.mul_le_mul cap ncap).trans cover

/-- Exponentiating a superadditive integer calendar gives a
supermultiplicative sequence of positive starting points. -/
theorem exponential_schedule (S : ℕ → ℕ) (super : ∀ i j, S i+S j ≤ S (i+j))
    (i j : ℕ) : 2^S i * 2^S j ≤ (2:ℕ)^S (i+j) := by
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by decide : 0<2) (super i j)

/-- The first interval ends at W*N(j), while the last starts at N(j+k−1).
In fact k≥2 suffices, and the conclusion is strict. -/
theorem transition_bound (N : ℕ → ℕ) {W j k m n : ℕ} (wpos : 0 < W)
    (start_pos : 0 < N j) (hk : 2 ≤ k)
    (super : ∀ i h, N i*N h ≤ N (i+h))
    (separated : ∀ i, 2*W*N i ≤ N (i+1))
    (first : n ≤ W*N j) (last : N (j+k-1) ≤ (2*m-1)*n) :
    N (k-2) < m := by
  have across := super j (k-1)
  rw [show j+(k-1)=j+k-1 by omega] at across
  have endCap := (across.trans last).trans (Nat.mul_le_mul_left (2*m-1) first)
  have one : N (k-1) ≤ (2*m-1)*W := by
    apply Nat.le_of_mul_le_mul_left _ start_pos
    calc N j*N (k-1) ≤ (2*m-1)*(W*N j) := endCap
      _ = N j*((2*m-1)*W) := by ring
  have gap := separated (k-2)
  rw [show k-2+1=k-1 by omega] at gap
  have twice : 2*N (k-2) ≤ 2*m-1 := by
    apply Nat.le_of_mul_le_mul_left _ wpos
    calc W*(2*N (k-2)) = 2*W*N (k-2) := by ring
      _ ≤ (2*m-1)*W := gap.trans one
      _ = W*(2*m-1) := Nat.mul_comm _ _
  have mono : Monotone N := by
    apply monotone_nat_of_le_succ
    intro i
    exact (by simpa using Nat.mul_le_mul_right (N i) (show 1 ≤ 2*W by omega) :
      N i ≤ 2*W*N i).trans (separated i)
  have hit := start_pos.trans_le (mono (show j ≤ j+k-1 by omega))
  have mp : 0 < m := by
    by_contra! h
    rw [show m=0 by omega] at last
    simp at last
    omega
  omega

#print axioms prefix_product
#print axioms exponential_schedule
#print axioms transition_bound
end Erdos142SelfProduct
