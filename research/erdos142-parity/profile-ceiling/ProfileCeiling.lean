import Mathlib

/-! Algebraic and integral steps for a translated-grid upper bound.
The numerical certificate and its exact integer replay are provided separately. -/
open Finset MeasureTheory
namespace Erdos142ProfileCeiling

theorem boxed_dual {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C x L U : ι → ℝ) (A : κ → ι → ℝ) (b μ : κ → ℝ)
    (box : ∀ j, L j ≤ x j ∧ x j ≤ U j) (non : ∀ i, 0 ≤ μ i)
    (satisfies : ∀ i, ∑ j, A i j*x j ≤ b i) :
    ∑ j, C j*x j ≤ (∑ i, μ i*b i) +
      ∑ j, max ((C j-∑ i, μ i*A i j)*L j) ((C j-∑ i, μ i*A i j)*U j) := by
  classical
  let r := fun j => C j-∑ i, μ i*A i j
  have boxcost (j : ι) : r j*x j ≤ max (r j*L j) (r j*U j) := by
    by_cases pos : 0 ≤ r j
    · exact (mul_le_mul_of_nonneg_left (box j).2 pos).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left (box j).1 (le_of_not_ge pos)).trans (le_max_left _ _)
  have matrix : ∑ j, (∑ i, μ i*A i j)*x j = ∑ i, μ i*(∑ j, A i j*x j) := by
    simp_rw [sum_mul,mul_sum,mul_assoc]
    rw [sum_comm]
  calc _ = ∑ j, ((∑ i, μ i*A i j)*x j+r j*x j) := by
         apply sum_congr rfl
         intro j _
         dsimp [r]; ring
       _ = (∑ i, μ i*(∑ j, A i j*x j)) + ∑ j, r j*x j := by rw [sum_add_distrib,matrix]
       _ ≤ _ := add_le_add (sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (satisfies i) (non i)))
         (sum_le_sum (fun j _ => boxcost j))

theorem translated_grid (f : ℝ → ℝ) (n : ℕ) (h : ℝ)
    (integrable : ∀ i : ℕ, i < n → IntervalIntegrable f volume ((i:ℝ)*h) (((i+1:ℕ):ℝ)*h)) :
    (∫ x in (0:ℝ)..((n:ℝ)*h), f x) =
      ∑ i ∈ range n, ∫ t in (0:ℝ)..h, f ((i:ℝ)*h+t) := by
  have split := intervalIntegral.sum_integral_adjacent_intervals (a := fun i:ℕ => (i:ℝ)*h) integrable
  simp only [Nat.cast_zero,zero_mul] at split
  rw [← split]
  apply sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_comp_add_left]
  simp only [add_zero,Nat.cast_succ,add_mul,one_mul]

end Erdos142ProfileCeiling
#print axioms Erdos142ProfileCeiling.boxed_dual
#print axioms Erdos142ProfileCeiling.translated_grid
