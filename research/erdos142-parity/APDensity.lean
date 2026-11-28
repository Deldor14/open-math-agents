import ProgressionDistribution

namespace ProgressionParity
open scoped BigOperators
open Filter Topology

noncomputable def APweight (k N:ℕ) (ε:ℝ) : ℝ := by
  classical
  exact if badAPDistribution k N ε then (N:ℝ)⁻¹ else 0

noncomputable def APlogMass (k X:ℕ) (ε:ℝ) : ℝ := ∑ n ∈ Finset.range X, APweight k n ε

private lemma APweight_nonnegative (k n:ℕ) (ε:ℝ) : 0≤APweight k n ε := by
  classical
  unfold APweight
  split <;> positivity

private lemma compare_mass {k D:ℕ} {ε δ:ℝ}
    (sub : ∀ n:ℕ, D≤n → badAPDistribution k n ε → badEndpoint k n δ) (X:ℕ) :
    APlogMass k X ε ≤ D+logMass k X δ := by
  classical
  have upper (n:ℕ) : APweight k n ε ≤ (if n<D then (1:ℝ) else 0)+badWeight k n δ := by
    by_cases lt : n<D
    · rw [if_pos lt]
      have nz : 0≤badWeight k n δ := by unfold badWeight;split <;> positivity
      have one : (n:ℝ)⁻¹≤1 := by
        by_cases z : n=0
        · simp [z]
        · apply inv_le_one_of_one_le₀
          exact_mod_cast (show 1≤n by omega)
      unfold APweight
      split <;> linarith
    · rw [if_neg lt,zero_add]
      by_cases flag : badAPDistribution k n ε
      · simp [APweight,badWeight,flag,sub n (by omega) flag]
      · simp [APweight,flag]
        unfold badWeight
        split <;> positivity
  have bound := Finset.sum_le_sum (s := Finset.range X) (fun n _ => upper n)
  rw [Finset.sum_add_distrib] at bound
  have sum : (∑ n ∈ Finset.range X, if n<D then (1:ℝ) else 0) ≤ D := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    have small := Finset.card_le_card (show (Finset.range X).filter (·<D) ⊆ Finset.range D from
      fun n hn => Finset.mem_range.mpr (Finset.mem_filter.mp hn).2)
    rw [Finset.card_range] at small
    exact_mod_cast small
  exact bound.trans (add_le_add sum (le_refl _))

theorem AP_logarithmic_mass_bound {ε:ℝ} (he : 0<ε) :
    ∃ C:ℝ, 0<C ∧ ∀ k:ℕ, 3≤k → ∀ X:ℕ, 2≤X → APlogMass k X ε ≤ C*Real.sqrt (Real.log X) := by
  obtain ⟨D,_,δ,hd,sub⟩ := AP_exceptional_subset he
  obtain ⟨C,cp,profile⟩ := logarithmic_mass_bound hd
  have lp : 0<Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
  refine ⟨C+D/Real.sqrt (Real.log 2),by positivity,?_⟩
  intro k hk X hx
  have lx := Real.log_le_log (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤X by exact_mod_cast hx)
  have compare := Real.sqrt_le_sqrt lx
  have fac : (D:ℝ) ≤ (D/Real.sqrt (Real.log 2))*Real.sqrt (Real.log X) := by
    have nn : (0:ℝ)≤D/Real.sqrt (Real.log 2) := by positivity
    have key := mul_le_mul_of_nonneg_left compare nn
    rwa [div_mul_cancel₀ _ lp.ne'] at key
  have h := compare_mass (sub k hk) X
  have pb := profile k hk X hx
  linarith only [h,pb,fac]

theorem AP_logarithmic_density_one {ε:ℝ} (he : 0<ε) {k:ℕ} (hk : 3≤k) :
    Tendsto (fun X:ℕ => APlogMass k X ε/Real.log X) atTop (𝓝 0) := by
  obtain ⟨C,_,bd⟩ := AP_logarithmic_mass_bound he
  have tends := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have lim : Tendsto (fun X:ℕ => C/Real.sqrt (Real.log X)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp tends).const_div_atTop C
  apply squeeze_zero' _ _ lim
  · filter_upwards [eventually_ge_atTop 2] with X hx
    have pos := Real.log_pos (show 1<(X:ℝ) by exact_mod_cast (show 1<X by omega))
    exact div_nonneg (Finset.sum_nonneg fun n _ => APweight_nonnegative k n ε) pos.le
  · filter_upwards [eventually_ge_atTop 2] with X hx
    have pos := Real.log_pos (show 1<(X:ℝ) by exact_mod_cast (show 1<X by omega))
    have sp := Real.sqrt_pos.mpr pos
    apply (div_le_div_iff₀ pos sp).mpr
    have h := mul_le_mul_of_nonneg_right (bd k hk X hx) sp.le
    nlinarith only [h,congrArg (C*·) (Real.mul_self_sqrt pos.le)]

#print axioms AP_logarithmic_mass_bound
#print axioms AP_logarithmic_density_one
end ProgressionParity
