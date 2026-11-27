import OMAStatements.S_oeis_a062071
import Mathlib

namespace Deldor14.ReciprocalFloors
open OMA.S_oeis_a062071 Filter Topology
private theorem pointwise (d : ℕ) (hd : 0<d) :
    Tendsto (fun n : ℕ => ((n/d:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1/(d:ℝ))) := by
  have dp : 0<(d:ℝ) := by exact_mod_cast hd
  have grow : Tendsto (fun n : ℕ => (n:ℝ)/d) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const dp
  have lim := (tendsto_nat_floor_div_atTop.comp grow).div_const (d:ℝ)
  simpa only [Function.comp_def,Nat.floor_div_eq_div,div_div,div_mul_cancel₀ _ dp.ne'] using lim

theorem reciprocalFloorAsymptotic (d : ℕ → ℕ) (hp : ∀ k,0<d k)
    (hs : Summable (fun k => 1/(d k:ℝ))) :
    Tendsto (fun n : ℕ => (∑' k,((n/d k:ℕ):ℝ))/((∑' k,1/(d k:ℝ))*(n:ℝ))) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => ∑' k, ((n/d k:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (∑' k,1/(d k:ℝ))) := by
    apply tendsto_tsum_of_dominated_convergence hs
    · exact fun k => pointwise (d k) (hp k)
    · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn k
      have dp : 0<(d k:ℝ) := by exact_mod_cast hp k
      have np : 0<(n:ℝ) := by exact_mod_cast hn
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      apply (div_le_div_iff₀ np dp).mpr
      simpa using (show ((n/d k:ℕ):ℝ)*d k ≤ n by exact_mod_cast Nat.div_mul_le_self n _)
  have pos (k : ℕ) : 0<1/(d k:ℝ) := by have := hp k;positivity
  have positive := hs.tsum_pos (fun k => (pos k).le) 0 (pos 0)
  have lim := h.div_const (∑' k,1/(d k:ℝ))
  rw [div_self positive.ne'] at lim
  simpa only [tsum_div_const,div_div,mul_comm] using lim
theorem result : type_of% @OMA.S_oeis_a062071.main := by
  apply reciprocalFloorAsymptotic denominator (by intro k;unfold denominator;positivity)
  have h := summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1:ℝ)/2<1)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ h
  intro k
  rw [div_pow,one_pow]
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast (show 2^k≤denominator k by
    cases k with
    | zero => decide
    | succ j =>
      unfold denominator
      exact (Nat.pow_le_pow_left (by omega : 2≤j+1+1) _).trans (Nat.pow_le_pow_right (by omega) (by omega)))
end Deldor14.ReciprocalFloors
theorem OMA.solution : type_of% @OMA.S_oeis_a062071.main := Deldor14.ReciprocalFloors.result
