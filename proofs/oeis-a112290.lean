import OMAStatements.S_oeis_a112290
import Mathlib

/-! The two endpoint Stirling numbers are one. Every interior number in
row n is at least n(n-1)/2, so the sum of the interior reciprocals tends
to zero. This proves Kotesovec's 2022 limit. -/
namespace Deldor14.StirlingReciprocals
open Nat Finset Filter OMA.S_oeis_a112290
open scoped Topology
private lemma lower (n k : ℕ) (hk : 2 ≤ k) (hn : k < n) :
    n*(n-1) ≤ 2*stirlingSecond n k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    by_cases eq : k=n
    · subst k
      rw [stirlingSecond_succ_self_left]
      have h := Nat.add_one_mul_choose_eq n 1
      simp only [choose_one_right] at h
      simp only [Nat.add_sub_cancel];nlinarith
    have h := ih k hk (by omega)
    have ge : n-1+1=n := by omega
    rw [stirlingSecond_succ_left n k (by omega),Nat.add_sub_cancel]
    nlinarith [Nat.mul_le_mul_right (stirlingSecond n k) hk, Nat.mul_le_mul_left n (show 2 ≤ n-1 by omega)]
private lemma errs (m : ℕ) : 2 ≤ (reciprocalSum (m+2):ℝ) ∧
    (reciprocalSum (m+2):ℝ) ≤ 2+2/(m+2:ℝ) := by
  let f (i : ℕ) : ℝ := (stirlingSecond (m+2) (i+2):ℝ)⁻¹
  have form : (reciprocalSum (m+2):ℝ)= 2+∑ i ∈ range m,f i := by
    unfold reciprocalSum
    push_cast
    rw [sum_range_succ,sum_range_succ' (fun i => (stirlingSecond (m+2) (i+1):ℝ)⁻¹)]
    simp only [f,zero_add,stirlingSecond_self,stirlingSecond_one_right,Nat.cast_one,inv_one]
    ring
  have point (i : ℕ) (hi : i∈range m) : f i ≤ 2/((m+2:ℝ)*(m+1)) := by
    have hm := mem_range.mp hi
    have h := lower (m+2) (i+2) (by omega) (by omega)
    rw [show m+2-1=m+1 by omega] at h
    have rc : (((m:ℝ)+2)*(m+1)) ≤ 2*(stirlingSecond (m+2) (i+2):ℝ) := by exact_mod_cast h
    have pos : (0:ℝ)<stirlingSecond (m+2) (i+2) := by nlinarith [mul_pos (by positivity : 0<(m:ℝ)+2) (by positivity : 0<(m:ℝ)+1)]
    dsimp [f];rw [←one_div,div_le_div_iff₀ pos (by positivity)];linarith
  have upper := sum_le_sum point
  simp only [sum_const,card_range,nsmul_eq_mul] at upper
  rw [form]
  constructor
  · have h : 0 ≤ ∑ i ∈ range m,f i := sum_nonneg (fun i _ => by dsimp [f];positivity)
    linarith
  · apply add_le_add le_rfl (upper.trans ?_)
    field_simp;linarith

theorem full : type_of% @OMA.S_oeis_a112290.main := by
  have lim : Tendsto (fun n : ℕ => (reciprocalSum n:ℝ)) atTop (𝓝 2) := by
    apply (tendsto_add_atTop_iff_nat 2).mp
    have z : Tendsto (fun m : ℕ => (2:ℝ)/(m+2)) atTop (𝓝 0) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat (2:ℝ)).comp (tendsto_add_atTop_nat 2)
      simpa [Function.comp_def] using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using z.const_add 2) (fun m => (errs m).1) (fun m => (errs m).2)
  simpa only [Rat.cast_def,numerator,denominator] using lim
end Deldor14.StirlingReciprocals
theorem OMA.solution : type_of% @OMA.S_oeis_a112290.main := Deldor14.StirlingReciprocals.full
