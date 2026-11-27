import OMAStatements.S_oeis_a038663
import Mathlib

namespace Deldor14.ReciprocalFib
open OMA.S_oeis_a038663 Filter Topology

private noncomputable def weight (k : ℕ) : ℝ := 1 / (Nat.fib (k+2):ℝ)
private theorem fibBound (k : ℕ) : (4/3:ℝ)^k ≤ Nat.fib (k+2) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 | 1 => norm_num [Nat.fib]
    | j+2 =>
      have h₁ := ih j (by omega)
      have h₂ := ih (j+1) (by omega)
      rw [Nat.fib_add_two (n:=j+2),Nat.cast_add]
      rw [pow_succ] at h₂
      rw [pow_succ,pow_succ]
      nlinarith [show 0≤(4/3:ℝ)^j by positivity]

private theorem weightPos (k : ℕ) : 0<weight k := by
  have h : 0 < Nat.fib (k+2) := Nat.fib_pos.mpr (by omega)
  unfold weight
  positivity

private theorem summ : Summable weight := by
  apply Summable.of_nonneg_of_le (fun k => (weightPos k).le) _ (summable_geometric_of_lt_one
    (by norm_num : 0≤(3/4:ℝ)) (by norm_num))
  intro k
  unfold weight
  rw [show (3/4:ℝ)=(4/3:ℝ)⁻¹ by norm_num,inv_pow,← one_div]
  exact one_div_le_one_div_of_le (by positivity) (fibBound k)
private theorem total : reciprocalConstant - 1 = ∑' k, weight k := by
  let f (k : ℕ) : ℝ := 1 / (Nat.fib (k+1):ℝ)
  have full : Summable f := (summable_nat_add_iff 1).mp (show Summable (fun k => f (k+1)) from summ)
  change (∑' k,f k)-1=_
  rw [full.tsum_eq_zero_add]
  have h : f 0 = 1 := by norm_num [f,Nat.fib]
  rw [h]
  change 1+(∑' k,weight k)-1=_
  ring

private theorem pointwise (d : ℕ) (hd : 0<d) :
    Tendsto (fun n : ℕ => ((n/d:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1/(d:ℝ))) := by
  have dp : 0<(d:ℝ) := by exact_mod_cast hd
  have grow : Tendsto (fun n : ℕ => (n:ℝ)/d) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const dp
  have lim := (tendsto_nat_floor_div_atTop.comp grow).div_const (d:ℝ)
  simpa only [Function.comp_def,Nat.floor_div_eq_div,div_div,div_mul_cancel₀ _ dp.ne'] using lim

theorem result : type_of% @OMA.S_oeis_a038663.main := by
  have h : Tendsto (fun n : ℕ => ∑' k, ((n/Nat.fib (k+2):ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (∑' k,weight k)) := by
    apply tendsto_tsum_of_dominated_convergence summ
    · intro k
      exact pointwise _ (Nat.fib_pos.mpr (by omega))
    · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn k
      have pd : 0<Nat.fib (k+2) := Nat.fib_pos.mpr (by omega)
      have dp : 0<(Nat.fib (k+2):ℝ) := by exact_mod_cast pd
      have np : 0<(n:ℝ) := by exact_mod_cast hn
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      apply (div_le_div_iff₀ np dp).mpr
      simpa using (show ((n/Nat.fib (k+2):ℕ):ℝ)*Nat.fib (k+2) ≤ n by exact_mod_cast Nat.div_mul_le_self n _)
  have positive := summ.tsum_pos (fun k => (weightPos k).le) 0 (weightPos 0)
  have lim := h.div_const (∑' k, weight k)
  rw [div_self positive.ne'] at lim
  rw [total]
  simpa only [value,tsum_div_const,div_div,mul_comm] using lim

end Deldor14.ReciprocalFib
theorem OMA.solution : type_of% @OMA.S_oeis_a038663.main := Deldor14.ReciprocalFib.result
