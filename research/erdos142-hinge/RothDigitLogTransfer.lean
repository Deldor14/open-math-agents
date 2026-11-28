import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Filter Topology Real

namespace Erdos142Review

/-- Changing a dimension by bounded multiplicative factors preserves its logarithmic
exponent, including along an arbitrary subsequence of input scales. -/
theorem comparable_log_scale {s g d : ℕ → ℝ} {β p a b : ℝ}
    (hs : Tendsto s atTop atTop) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hβ : Tendsto (fun n => log (g n) / log (s n)) atTop (𝓝 β))
    (ha : 0<a) (hb : 0<b)
    (hcomp : ∀ᶠ n in atTop,
      a * (s n / g n)^p ≤ d n ∧ d n ≤ b * (s n / g n)^p) :
    Tendsto (fun n => log (d n) / log (s n)) atTop (𝓝 (p*(1-β))) := by
  have hlog := Real.tendsto_log_atTop.comp hs
  have haff (c : ℝ) :
      Tendsto (fun n => c/log (s n)+p*(1-log (g n)/log (s n)))
        atTop (𝓝 (p*(1-β))) := by
    simpa using (hlog.const_div_atTop c).add
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub hβ) :
        Tendsto (fun n => p*(1-log (g n)/log (s n))) atTop _)
  have hform (c : ℝ) (hc : 0<c) :
      Tendsto (fun n => log (c*(s n/g n)^p)/log (s n)) atTop (𝓝 (p*(1-β))) := by
    apply (haff (log c)).congr'
    filter_upwards [hs.eventually_gt_atTop 1, hg] with n hn hgn
    have hsn : 0<s n := by linarith
    have hquot : 0<s n/g n := div_pos hsn hgn
    rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos hquot p).ne',
        Real.log_rpow hquot,Real.log_div hsn.ne' hgn.ne']
    field_simp [ne_of_gt (Real.log_pos hn)]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hform a ha) (hform b hb)
  · filter_upwards [hs.eventually_gt_atTop 1,hg,hcomp] with n hn hgn hc
    have hsn : 0<s n := by linarith
    exact div_le_div_of_nonneg_right (Real.log_le_log (by positivity) hc.1)
      (Real.log_pos hn).le
  · filter_upwards [hs.eventually_gt_atTop 1,hg,hcomp] with n hn hgn hc
    have hsn : 0<s n := by linarith
    have hd : 0<d n := lt_of_lt_of_le (by positivity) hc.1
    exact div_le_div_of_nonneg_right (Real.log_le_log hd hc.2) (Real.log_pos hn).le

/-- Eliminate the input scale from the two log-ratios. -/
theorem eliminate_input_scale {s g d : ℕ → ℝ} {β p : ℝ}
    (hs : Tendsto s atTop atTop)
    (hg : Tendsto (fun n => log (g n)/log (s n)) atTop (𝓝 β))
    (hd : Tendsto (fun n => log (d n)/log (s n)) atTop (𝓝 (p*(1-β))))
    (hne : p*(1-β)≠0) :
    Tendsto (fun n => log (g n)/log (d n)) atTop (𝓝 (β/(p*(1-β)))) := by
  apply (hg.div hd hne).congr'
  filter_upwards [hs.eventually_gt_atTop 1] with n hn
  change (log (g n)/log (s n))/(log (d n)/log (s n)) = _
  rw [div_div_div_cancel_right₀ (ne_of_gt (Real.log_pos hn))]

/-- A computed real dimension can be rounded up to an actual integer dimension. -/
theorem ceiling_scale {s g : ℕ → ℝ} {β p C : ℝ}
    (hs : Tendsto s atTop atTop) (hg : ∀ᶠ n in atTop, 0<g n)
    (hβ : Tendsto (fun n => log (g n)/log (s n)) atTop (𝓝 β))
    (hC : 0<C) (hpos : 0<p*(1-β)) :
    let d := fun n => (⌈C*(s n/g n)^p⌉₊ : ℝ)
    Tendsto d atTop atTop ∧
    Tendsto (fun n => log (d n)/log (s n)) atTop (𝓝 (p*(1-β))) ∧
    Tendsto (fun n => log (g n)/log (d n)) atTop (𝓝 (β/(p*(1-β)))) := by
  let z := fun n => C*(s n/g n)^p
  have hz : Tendsto (fun n => log (z n)/log (s n)) atTop (𝓝 (p*(1-β))) :=
    comparable_log_scale hs hg hβ hC hC (Eventually.of_forall fun _ => ⟨le_rfl,le_rfl⟩)
  have hlog : Tendsto (fun n => log (z n)) atTop atTop := by
    apply (hz.pos_mul_atTop hpos (Real.tendsto_log_atTop.comp hs)).congr'
    filter_upwards [hs.eventually_gt_atTop 1] with n hn
    change log (z n) / log (s n) * log (s n) = _
    exact div_mul_cancel₀ _ (Real.log_pos hn).ne'
  have hzpos : ∀ᶠ n in atTop, 0<z n := by
    filter_upwards [hs.eventually_gt_atTop 0,hg] with n hn hgn
    dsimp [z]
    positivity
  have hzinf : Tendsto z atTop atTop := by
    refine (Real.tendsto_exp_atTop.comp hlog).congr' ?_
    filter_upwards [hzpos] with n hn
    exact Real.exp_log hn
  let d := fun n => (⌈z n⌉₊ : ℝ)
  have hdinf : Tendsto d atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_ceil (z n)) hzinf
  have hd : Tendsto (fun n => log (d n)/log (s n)) atTop (𝓝 (p*(1-β))) := by
    apply comparable_log_scale hs hg hβ hC (show 0<2*C by positivity)
    filter_upwards [hzinf.eventually_ge_atTop 1] with n hn
    refine ⟨Nat.le_ceil (z n),?_⟩
    have hlt := Nat.ceil_lt_add_one (show 0≤z n by linarith)
    change (⌈z n⌉₊ : ℝ) ≤ 2*C*(s n/g n)^p
    change 1≤C*(s n/g n)^p at hn
    dsimp [z] at hlt ⊢
    linarith
  exact ⟨hdinf,hd,eliminate_input_scale hs hβ hd hpos.ne'⟩

/-- Exact normalization for the dimension of a guarded product. -/
theorem guarded_dimension_identity {x g θ p : ℝ}
    (hx : 0<x) (hg : 0<g) (hp : θ*p+1=p) :
    x*(x^θ/g)^p = (x/g)^p := by
  rw [div_rpow (rpow_pos_of_pos hx θ).le hg.le,div_rpow hx.le hg.le,
      ←rpow_mul hx.le,←mul_div_assoc,mul_comm x,←rpow_add_one hx.ne',hp]

/-- The final factor of t+1 and the max with one still work if the optimal
number of digits stays bounded. This includes the square-root endpoint. -/
theorem guarded_dimension_comparison {x g θ p c : ℝ} (hx : 1≤x) (hg : 0<g)
    (hc : 0<c) (hp : θ*p+1=p) (hlower : c≤(x^θ/g)^p) :
    let w := (x^θ/g)^p
    let d := (max 1 ⌊w⌋₊ : ℕ)*(x+1)
    (1/2:ℝ)*(x/g)^p ≤ d ∧ d ≤ (2*(1+1/c))*(x/g)^p := by
  let w := (x^θ/g)^p
  let m : ℝ := ↑(max 1 ⌊w⌋₊ : ℕ)
  have hw : 0<w := lt_of_lt_of_le hc hlower
  have hf := Nat.lt_floor_add_one w
  have hf' := Nat.floor_le hw.le
  have hm : m = max 1 (⌊w⌋₊ : ℝ) := by simp [m]
  have hmf : (⌊w⌋₊ : ℝ)≤m := by rw [hm]; exact le_max_right _ _
  have hm1 : 1≤m := by rw [hm]; exact le_max_left _ _
  have hlo : w/2≤m := by linarith
  have h1 : 1≤w/c := (le_div_iff₀ hc).2 (by simpa using hlower)
  have hhi : m≤w+w/c := by
    rw [hm]; apply max_le <;> linarith
  have hid : x*w=(x/g)^p := guarded_dimension_identity (by linarith) hg hp
  change 1/2*(x/g)^p≤m*(x+1) ∧ m*(x+1)≤2*(1+1/c)*(x/g)^p
  rw [←hid]
  constructor
  · calc
      1/2*(x*w) = (w/2)*x := by ring
      _ ≤ m*(x+1) := by gcongr; linarith
  · calc
      m*(x+1) ≤ (w+w/c)*(2*x) := by gcongr; linarith
      _ = 2*(1+1/c)*(x*w) := by ring

/-- Apply the log comparison directly to the guarded dimension in the digit
construction. The lower bound on the unrounded digit count can be any positive
constant; it need not diverge along the subsequence. -/
theorem guarded_scale_change {s g : ℕ → ℝ} {β θ p c : ℝ}
    (hs : Tendsto s atTop atTop) (hg : ∀ᶠ n in atTop, 0<g n)
    (hβ : Tendsto (fun n => log (g n)/log (s n)) atTop (𝓝 β))
    (hc : 0<c) (hp : θ*p+1=p) (hn : p*(1-β)≠0)
    (hlower : ∀ᶠ n in atTop, c≤((s n)^θ/g n)^p) :
    let d := fun n => (max 1 ⌊((s n)^θ/g n)^p⌋₊ : ℕ)*(s n+1)
    Tendsto (fun n => log (d n)/log (s n)) atTop (𝓝 (p*(1-β))) ∧
    Tendsto (fun n => log (g n)/log (d n)) atTop (𝓝 (β/(p*(1-β)))) := by
  intro d
  have hd : Tendsto (fun n => log (d n)/log (s n)) atTop (𝓝 (p*(1-β))) := by
    apply comparable_log_scale hs hg hβ (show (0:ℝ)<1/2 by norm_num)
      (show 0<2*(1+1/c) by positivity)
    filter_upwards [hs.eventually_ge_atTop 1,hg,hlower] with n hsn hgn hb
    exact guarded_dimension_comparison hsn hgn hc hp hb
  exact ⟨hd,eliminate_input_scale hs hβ hd hn⟩

/-- Every integer scale is reached by the fractional floor map. This gives
an explicit right inverse, including at zero and at exponent one. -/
theorem floor_power_right_inverse (t : ℕ) {a : ℝ} (ha : 0<a) (ha' : a≤1) :
    ⌊((⌈(t:ℝ)^(1/a)⌉₊ : ℕ):ℝ)^a⌋₊=t := by
  let x := (t:ℝ)^(1/a)
  have hx : 0≤x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have heq : x^a = (t:ℝ) := by
    dsimp [x]
    rw [←Real.rpow_mul (Nat.cast_nonneg _),one_div_mul_cancel ha.ne', Real.rpow_one]
  apply (Nat.floor_eq_iff (Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
  constructor
  · exact heq.ge.trans (Real.rpow_le_rpow hx (Nat.le_ceil x) ha.le)
  · calc
      ((⌈x⌉₊ : ℕ):ℝ)^a < (x+1)^a :=
          Real.rpow_lt_rpow (Nat.cast_nonneg _) (Nat.ceil_lt_add_one hx) ha
      _ ≤ x^a+(1:ℝ)^a := Real.rpow_add_le_add_rpow hx zero_le_one ha.le ha'
      _ = _ := by rw [heq,Real.one_rpow]

end Erdos142Review

#print axioms Erdos142Review.comparable_log_scale
#print axioms Erdos142Review.eliminate_input_scale

#print axioms Erdos142Review.ceiling_scale

#print axioms Erdos142Review.guarded_dimension_identity
#print axioms Erdos142Review.guarded_dimension_comparison
#print axioms Erdos142Review.guarded_scale_change

#print axioms Erdos142Review.floor_power_right_inverse
