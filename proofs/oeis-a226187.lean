import OMAStatements.S_oeis_a226187
import Mathlib

/-! At the first crossing, the overshoot is at most the last harmonic
increment. Subtracting the Euler–Mascheroni asymptotic at adjacent crossings
gives the limiting logarithmic ratio. -/
namespace Deldor14.HarmonicCrossings
open Filter Topology Real OMA.S_oeis_a226187
private lemma spec (n : ℕ) : 0 < firstAbove n ∧ (n:ℝ)/3 < harmonic (firstAbove n) := by
  apply Nat.sInf_mem (s:={j : ℕ | 0 < j ∧ (n:ℝ)/3 < (harmonic j:ℝ)})
  obtain ⟨k,hk⟩ := exists_nat_gt (Real.exp ((n:ℝ)/3))
  refine ⟨k,?_,?_⟩
  · exact_mod_cast (Real.exp_pos _).trans hk
  · apply lt_of_lt_of_le _ (log_add_one_le_harmonic k)
    apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
    push_cast
    linarith
private lemma diverge : Tendsto firstAbove atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (3*(k+1))] with n hn
  by_contra! bad
  have f:=spec n
  have h:=harmonic_le_one_add_log (firstAbove n)
  have l:=Real.log_le_sub_one_of_pos (show (0:ℝ)<firstAbove n by exact_mod_cast f.1)
  have h' : (firstAbove n:ℝ)<k := by exact_mod_cast bad
  have hn' : (3:ℝ)*(k+1)≤n := by exact_mod_cast hn
  linarith [f.2]
private lemma overshoot (n : ℕ) : (harmonic (firstAbove n):ℝ) - (n:ℝ)/3 ≤ (firstAbove n:ℝ)⁻¹ := by
  obtain ⟨k,eq⟩ : ∃ k,firstAbove n=k+1 := ⟨firstAbove n-1,by have := (spec n).1; omega⟩
  have prev : (harmonic k:ℝ) ≤ (n:ℝ)/3 := by
    by_cases z : k=0
    · subst k;simp <;> positivity
    by_contra! bad
    have := Nat.sInf_le (show k ∈ {j : ℕ | 0 < j ∧ (n:ℝ)/3 < (harmonic j:ℝ)} from ⟨by omega,bad⟩)
    change firstAbove n ≤ k at this
    omega
  rw [eq,harmonic_succ]
  push_cast
  linarith
theorem result : type_of% @OMA.S_oeis_a226187.main := by
  have oh : Tendsto (fun n : ℕ => (harmonic (firstAbove n):ℝ)-(n:ℝ)/3) atTop (𝓝 0) := by
    exact squeeze_zero (fun n => (sub_nonneg.mpr (spec n).2.le)) overshoot
      (tendsto_inv_atTop_nhds_zero_nat.comp diverge)
  have eh := Real.tendsto_harmonic_sub_log.comp diverge
  have corr : Tendsto (fun n : ℕ => log (firstAbove n) - (n:ℝ)/3) atTop (𝓝 (-eulerMascheroniConstant)) := by
    convert oh.sub eh using 1 <;> first | (ext n; dsimp;ring) | ring
  have d := ((corr.comp (tendsto_add_atTop_nat 1)).sub corr).add (tendsto_const_nhds (x:=(1/3:ℝ)))
  have l : Tendsto (fun n : ℕ => log (firstAbove (n+1)) - log (firstAbove n)) atTop (𝓝 (1/3:ℝ)) := by
    convert d using 1 <;> first | (ext n; dsimp;push_cast;ring) | ring
  have e := (Real.continuous_exp.tendsto _).comp l
  convert e using 1
  ext n
  dsimp
  rw [Real.exp_sub,Real.exp_log (by exact_mod_cast (spec (n+1)).1),Real.exp_log (by exact_mod_cast (spec n).1)]
end Deldor14.HarmonicCrossings
theorem OMA.solution : type_of% @OMA.S_oeis_a226187.main := Deldor14.HarmonicCrossings.result
