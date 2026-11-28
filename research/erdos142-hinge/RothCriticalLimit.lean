import Mathlib

open Finset
namespace Erdos142CriticalLimit

/-- In a child edge with finite optimum scores, omit a cheapest child to
satisfy the parent. Scores are normalized by subtracting the excluded score. -/
theorem least_omission {α : Type*} [DecidableEq α] (C : Finset α)
    (nonempty : C.Nonempty) (gain : α → ℕ) :
    ∃ j ∈ C, (∀ i ∈ C, gain j ≤ gain i) ∧
      (∀ S ⊆ C, S ≠ C → gain j ≤ ∑ i ∈ C \ S, gain i) ∧
      (∑ i ∈ C \ (C.erase j), gain i) = gain j := by
  obtain ⟨j,hj,hmin⟩ := C.exists_min_image gain nonempty
  refine ⟨j,hj,hmin,?_,?_⟩
  · intro S sub proper
    have missing : ∃ i ∈ C, i ∉ S := by
      by_contra! h
      exact proper (Subset.antisymm sub h)
    obtain ⟨i,hi,notin⟩ := missing
    exact (hmin i hi).trans (single_le_sum (f := gain) (fun _ _ => Nat.zero_le _)
      (mem_sdiff.mpr ⟨hi,notin⟩))
  · have e : C \ C.erase j = {j} := by
      ext i
      by_cases h : i=j <;> simp_all
    simp [e]

theorem root_gain {α : Type*} (I : Finset α) (penalty : α → ℕ) (base : ℕ) :
    max base (base+1-∑ i ∈ I, penalty i) - base =
      if ∀ i ∈ I, penalty i=0 then 1 else 0 := by
  classical
  split_ifs with h
  · have e : (∑ i ∈ I, penalty i) = 0 := sum_eq_zero (fun i hi => h i hi)
    omega
  · push Not at h
    obtain ⟨i,hi,hpos⟩ := h
    have z := single_le_sum (f := penalty) (fun _ _ => Nat.zero_le _) hi
    omega

/-- Integrand estimate in the square-root log-probability metric. -/
theorem contraction_integrand {α : Type*} (I : Finset α) (g : α → ℝ) :
    Real.exp (-(∑ i ∈ I, g i^2)) * (∑ i ∈ I, g i)^2 ≤
       I.card * Real.exp (-1) := by
  have cs : (∑ i ∈ I, g i)^2 ≤ (I.card:ℝ) * ∑ i ∈ I, g i^2 :=
    sq_sum_le_card_mul_sum_sq
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left cs (Real.exp_nonneg _)
    _ = (I.card:ℝ) * ((∑ i ∈ I, g i^2)*Real.exp (-(∑ i ∈ I, g i^2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.mul_exp_neg_le_exp_neg_one _) (by positivity)

/-- Counting each derivative at a non-root position gives the cavity cancellation. -/
theorem edge_derivative (k rate B dA dB : ℝ)
    (h : dA = -k*B-rate*(k-1)*dB) : dA+(k-1)*(B+rate*dB) = -B := by
  rw [h]; ring

theorem anchor_intensity (x : ℝ) :
    (1-x)/2+min x (1-x)+x/2 ≤ 1 := by
  have a := min_le_left x (1-x)
  have b := min_le_right x (1-x)
  linarith

/-- Retaining the individual direction components gives the positive child
operator in the weighted contraction norm. -/
theorem weighted_integrand {α : Type*} (I : Finset α) (g h : α → ℝ) :
    Real.exp (-(∑ i ∈ I, g i^2)) * (∑ i ∈ I, g i*h i)^2 ≤
      Real.exp (-1) * ∑ i ∈ I, h i^2 := by
  have cs := sum_mul_sq_le_sq_mul_sq I g h
  calc
    _ ≤ Real.exp (-(∑ i ∈ I, g i^2)) * ((∑ i ∈ I, g i^2) * ∑ i ∈ I, h i^2) :=
      mul_le_mul_of_nonneg_left cs (Real.exp_nonneg _)
    _ = ((∑ i ∈ I, g i^2) * Real.exp (-(∑ i ∈ I, g i^2))) * ∑ i ∈ I, h i^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.mul_exp_neg_le_exp_neg_one _)
      (sum_nonneg (fun _ _ => sq_nonneg _))

#print axioms weighted_integrand
#print axioms least_omission
#print axioms root_gain
#print axioms contraction_integrand
#print axioms edge_derivative
#print axioms anchor_intensity

end Erdos142CriticalLimit
