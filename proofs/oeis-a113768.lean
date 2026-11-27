import OMAStatements.S_oeis_a113768
import Mathlib

namespace Deldor14.CubeGrowth
open OMA.S_oeis_a113768 Filter Topology Finset

private noncomputable def r (n : ℕ) := (value n:ℝ)^(1/3:ℝ)
private noncomputable def q (n : ℕ) : ℝ := ⌊r n⌋₊
private theorem increment (n : ℕ) : (value (n+1):ℝ)=value n+q n := by simp [value,q,r]
private theorem lower (n : ℕ) : n+1≤value n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h : 1≤(value n:ℝ) := by exact_mod_cast (show 1≤value n by omega)
    have h₁ : 1≤r n := Real.one_le_rpow h (by norm_num)
    have h₂ : 1≤⌊r n⌋₊ := (Nat.le_floor_iff (by positivity : 0≤r n)).mpr (by simpa)
    change n+1+1≤value n+⌊r n⌋₊
    omega
private theorem rp (n : ℕ) : 0<r n := by
  have hn : 0<(value n:ℝ) := by exact_mod_cast (show 0<value n by have := lower n; omega)
  exact Real.rpow_pos_of_pos hn _
private theorem cube (n : ℕ) : (r n)^3=value n := by
  unfold r
  rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
  norm_num
private theorem infinity : Tendsto r atTop atTop := by
  have grow : Tendsto (fun n : ℕ => (value n:ℝ)) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    exact fun n => by exact_mod_cast (show n≤value n by have := lower n; omega)
  exact (tendsto_rpow_atTop (by norm_num : 0<(1/3:ℝ))).comp grow
private theorem floorRatio : Tendsto (fun n => q n/r n) atTop (𝓝 1) :=
  tendsto_nat_floor_div_atTop.comp infinity

private theorem rootRatio : Tendsto (fun n => r (n+1)/r n) atTop (𝓝 1) := by
  have tiny := floorRatio.mul (infinity.inv_tendsto_atTop.pow 2)
  have raw : Tendsto (fun n => (value (n+1):ℝ)/value n) atTop (𝓝 1) := by
    have eq (n : ℕ) : (value (n+1):ℝ)/value n = 1 + (q n/r n)*((r n)⁻¹)^2 := by
      rw [increment,← cube]
      field_simp [(rp n).ne']
      <;> ring
    simp only [eq]
    convert (tendsto_const_nhds (x:=(1:ℝ))).add tiny using 1 <;> norm_num
  have outer := (Real.continuousAt_rpow_const (1:ℝ) (1/3) (Or.inl one_ne_zero)).tendsto.comp raw
  have eq (n : ℕ) : ((value (n+1):ℝ)/value n)^(1/3:ℝ)=r (n+1)/r n :=
    Real.div_rpow (Nat.cast_nonneg (value (n+1))) (Nat.cast_nonneg (value n)) (1/3:ℝ)
  simpa only [Function.comp_def,eq,Real.one_rpow] using outer

private theorem diffLim : Tendsto (fun n => r (n+1)^2-r n^2) atTop (𝓝 (2/3)) := by
  let s (n : ℕ) := r (n+1)/r n
  have hs : Tendsto s atTop (𝓝 1) := rootRatio
  have raw := (floorRatio.mul (hs.add_const 1)).div (((hs.pow 2).add hs).add_const 1) (by norm_num)
  have eq (n : ℕ) : r (n+1)^2-r n^2 = (q n/r n)*(s n+1)/(s n^2+s n+1) := by
    have h : r (n+1)^3=r n^3+q n := by rw [cube,cube,increment]
    have ha := rp n
    have hb := rp (n+1)
    have pos : 0<s n := div_pos hb ha
    have nz : s n^2+s n+1≠0 := by positivity
    apply (eq_div_iff nz).2
    dsimp [s]
    field_simp [ha.ne']
    nlinarith [congrArg (fun z : ℝ => z*(r (n+1)+r n)) h]
  simp only [eq]
  convert raw using 1 <;> first | rfl | norm_num

private theorem scaled : Tendsto (fun n : ℕ => r n^2/((n:ℝ)+1)) atTop (𝓝 (2/3)) := by
  have sums (n : ℕ) : (∑ i ∈ range n, (r (i+1)^2-r i^2))=r n^2-1 := by
    induction n with
    | zero => norm_num [r,value]
    | succ k ih => rw [sum_range_succ,ih]; ring
  have avg := diffLim.cesaro
  simp only [sums] at avg
  have grow : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop := tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have small := grow.inv_tendsto_atTop
  have h := (((tendsto_const_nhds (x:=(1:ℝ))).sub small).mul avg).add small
  have eq : (fun n : ℕ => (1-((n:ℝ)+1)⁻¹)*((n:ℝ)⁻¹*(r n^2-1))+((n:ℝ)+1)⁻¹) =ᶠ[atTop]
       fun n => r n^2/((n:ℝ)+1) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hn' : (n:ℝ)≠0 := by positivity
    field_simp [hn',show (n:ℝ)+1≠0 by positivity]
    <;> ring
  simpa using h.congr' eq

theorem result : type_of% @OMA.S_oeis_a113768.main := by
  have h := scaled.mul (Real.continuous_sqrt.continuousAt.tendsto.comp scaled)
  have eq (n : ℕ) : (value n:ℝ)/(((n:ℝ)+1)*Real.sqrt ((n:ℝ)+1))=
      (r n^2/((n:ℝ)+1))*Real.sqrt (r n^2/((n:ℝ)+1)) := by
    rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (rp n).le,← cube]
    field_simp
    <;> ring
  simpa only [eq,Function.comp_def] using h
end Deldor14.CubeGrowth
theorem OMA.solution : type_of% @OMA.S_oeis_a113768.main := Deldor14.CubeGrowth.result
