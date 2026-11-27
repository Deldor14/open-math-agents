import OMAReductions.R_Green82_green_82_lower_bound_R1
import Mathlib
open Real Filter Asymptotics
open scoped Topology

theorem OMA.solution : OMA.R_Green82_green_82_lower_bound_R1.H1 := by
  intro c hc
  change
    ∃ o : ℕ → ℝ, o =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ᶠ n : ℕ in atTop, (log (log n))^(1-|o n|) ≤ c*log (log n)/log (log (log n))
  let x (n : ℕ) := log (log n)
  let y (n : ℕ) := log (x n)
  let o (n : ℕ) := (log (y n)-log c)/y n
  have xn : Tendsto x atTop atTop := tendsto_log_atTop.comp (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have yn : Tendsto y atTop atTop := tendsto_log_atTop.comp xn
  have l₁ := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp yn
  have l₂ : Tendsto (fun n => log c*(y n)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=log c)).mul yn.inv_tendsto_atTop
  have lim : Tendsto o atTop (𝓝 0) := by
    have v := l₁.sub l₂
    simpa [o,sub_div,div_eq_mul_inv,sub_mul,Function.comp_def] using v
  refine ⟨o,(isLittleO_one_iff ℝ).mpr lim,?_⟩
  filter_upwards [xn.eventually_gt_atTop 1,yn.eventually_gt_atTop 0] with n hx hy
  change (x n)^(1-|o n|)≤c*x n/y n
  apply (Real.rpow_le_rpow_of_exponent_le hx.le (sub_le_sub_left (le_abs_self (o n)) 1)).trans
  have xp : 0<x n := by linarith
  rw [rpow_def_of_pos xp]
  have ex : log (x n)*(1-o n)=log (x n)-(log (y n)-log c) := by
    change y n*(1-(log (y n)-log c)/y n)=y n-(log (y n)-log c)
    field_simp [hy.ne']
  rw [ex,exp_sub,exp_log xp,exp_sub,exp_log hy,exp_log hc]
  apply le_of_eq
  field_simp
