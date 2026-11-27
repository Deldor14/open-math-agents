import OMAStatements.S_oeis_a076902
import Mathlib

namespace Deldor14.HalvingError
open OMA.S_oeis_a076902 Filter Topology
private noncomputable def err (n : ℕ) : ℝ := (a n:ℝ)-(n:ℝ)/3
private theorem bound (n : ℕ) (hn : 0<n) : |err n|<Real.log ((n:ℝ)+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases one : n=1
    · subst n
      have base : a 1=1 := by rw [a,if_pos (by decide)];rfl
      norm_num [err,base]
      linarith [Real.log_two_gt_d9]
    let k := n/2
    have hk : 0<k := by dsimp [k];omega
    have e := ih k (by dsimp [k];omega) hk
    have recA : (a n:ℝ)=(k:ℝ)-(a k:ℝ) := by
      rw [a,if_neg (by omega)]
      push_cast
      rfl
    have split : n=2*k ∨ n=2*k+1 := by dsimp [k];omega
    rcases split with he|he
    · have eq : err n= -err k := by unfold err;rw [recA];rw [he];push_cast;ring
      rw [eq,abs_neg]
      exact e.trans_le (Real.log_le_log (by positivity) (by exact_mod_cast (show k+1≤n+1 by omega)))
    · have eq : err n= -err k-1/3 := by unfold err;rw [recA];rw [he];push_cast;ring
      have add := abs_sub (-err k) (1/3)
      rw [abs_neg,abs_of_nonneg (by norm_num : 0≤(1/3:ℝ))] at add
      have scale : (n:ℝ)+1=2*((k:ℝ)+1) := by rw [he];push_cast;ring
      rw [eq,scale,Real.log_mul (by norm_num) (by positivity)]
      linarith [Real.log_two_gt_d9]
theorem result : type_of% @OMA.S_oeis_a076902.main := by
  refine ⟨bound,?_⟩
  have inv := (tendsto_natCast_atTop_atTop (R:=ℝ)).inv_tendsto_atTop
  have logs := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have lim : Tendsto (fun n : ℕ => 3*(Real.log 2*(n:ℝ)⁻¹+Real.log (n:ℝ)/(n:ℝ))) atTop (𝓝 0) := by
    convert ((tendsto_const_nhds (x:=(3:ℝ))).mul (((tendsto_const_nhds (x:=Real.log 2)).mul inv).add logs)) using 1 <;> first | rfl | norm_num
  have scaled : Tendsto (fun n : ℕ => (a n:ℝ)/((n:ℝ)/3)-1) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ lim
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have np : 0<(n:ℝ) := by exact_mod_cast hn
    have high : Real.log ((n:ℝ)+1)≤Real.log 2+Real.log (n:ℝ) := by
      rw [← Real.log_mul (by norm_num) np.ne']
      apply Real.log_le_log (by positivity)
      have z : (1:ℝ)≤n := by exact_mod_cast hn
      linarith
    have e := (bound n hn).le.trans high
    have eq : (a n:ℝ)/((n:ℝ)/3)-1=3*(err n)/(n:ℝ) := by
      unfold err
      field_simp [np.ne']
      <;> ring
    rw [Real.norm_eq_abs,eq,abs_div,abs_mul,abs_of_pos np,abs_of_nonneg (by norm_num : (0:ℝ)≤3)]
    calc
      _ ≤ 3*(Real.log 2+Real.log (n:ℝ))/(n:ℝ) := by gcongr
      _ = _ := by ring
  have h := scaled.add_const 1
  simpa using h
end Deldor14.HalvingError
theorem OMA.solution : type_of% @OMA.S_oeis_a076902.main := Deldor14.HalvingError.result
