import RegularScales
import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib

/-! Absolute losses between consecutive dyadic scales cannot be bounded by
a sublinear fixed power at every large scale. General density-zero criterion,
with the unconditioned application to upstream r_3 via mathlib's Roth theorem. -/
namespace Erdos142Loss
open Filter Topology Asymptotics Finset ProgressionParity Set.IsAPOfLengthFree

theorem upstream_three_eq_roth (n : ℕ) : maxCard 3 n = rothNumberNat n := by
  apply le_antisymm _ (roth_le_upstream n)
  obtain ⟨A,ha,fa,ca⟩ := attained (by decide : 1<3) n
  have hf : ThreeAPFree (A:Set ℕ) := by
    intro x hx y hy z hz eq
    by_contra ne
    by_cases xy : x<y
    · apply fa x (y-x) (by omega)
      simpa [Run,show x+(y-x)=y by omega,show y+(y-x)=z by omega] using And.intro hx (And.intro hy hz)
    · apply fa z (y-z) (by omega)
      simpa [Run,show z+(y-z)=y by omega,show y+(y-z)=x by omega] using And.intro hz (And.intro hy hx)
  have b := hf.le_addRothNumber (t := Ico 1 (n+1)) (by
    intro x hx; obtain ⟨lx,ux⟩ := mem_Icc.mp (ha hx); exact mem_Ico.mpr ⟨lx,by omega⟩)
  rw [addRothNumber_Ico] at b
  simpa [ca] using b

noncomputable def size (k j : ℕ) : ℝ := maxCard k (2^j)
noncomputable def gap (k j : ℕ) : ℝ := 2*size k j-size k (j+1)

theorem roth_density_zero : Tendsto (fun j => size 3 j/(2:ℝ)^j) atTop (𝓝 0) := by
  have h := (isLittleO_iff_tendsto' (f := fun n : ℕ => (rothNumberNat n:ℝ))
    (g := fun n : ℕ => (n:ℝ)) (l := atTop) (by filter_upwards [eventually_ge_atTop 1] with n hn; simp [show n≠0 by omega])).mp rothNumberNat_isLittleO_id
  have seq := h.comp (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1<(2:ℕ)))
  simpa [Function.comp_def,size,upstream_three_eq_roth] using seq

/-- Every base strictly below two is eventually exceeded, at each fixed length. -/
theorem capacity {k : ℕ} (hk : 3 ≤ k) {s : ℝ} (hs : 0<s) (h2 : s<2) :
    ∀ᶠ j : ℕ in atTop, s^j ≤ size k j := by
  let d := Real.log 2-Real.log s
  have dp : 0<d := sub_pos.mpr (Real.log_lt_log hs h2)
  obtain ⟨J,hJ⟩ := exists_nat_gt (16*Real.log 2/d^2)
  filter_upwards [eventually_ge_atTop J] with j hj
  have j0 : 0≤(j:ℝ) := by positivity
  have hj' : (J:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have step := (div_lt_iff₀ (sq_pos_of_pos dp)).mp (hJ.trans_le hj')
  have ls : 0 ≤ (j:ℝ)*Real.log 2 := mul_nonneg j0 (Real.log_nonneg (by norm_num))
  have root := Real.sq_sqrt ls
  have cmp : 4*Real.sqrt ((j:ℝ)*Real.log 2) ≤ d*j := by
    have sq := mul_le_mul_of_nonneg_right step.le j0
    apply (sq_le_sq₀ (by positivity) (mul_nonneg dp.le j0)).mp
    rw [mul_pow,Real.sq_sqrt ls]
    nlinarith only [sq]
  have lower := (Behrend.roth_lower_bound (N := 2^j)).trans
    (show (rothNumberNat (2^j):ℝ) ≤ size k j by
      unfold size
      exact_mod_cast (roth_le_upstream (2^j)).trans (length_mono (by decide : 1<3) hk _))
  rw [Nat.cast_pow,Real.log_pow] at lower
  have power (x : ℝ) (hx : 0<x) : x^j=Real.exp ((j:ℝ)*Real.log x) := by
    rw [Real.exp_nat_mul,Real.exp_log hx]
  apply le_trans _ lower
  push_cast
  rw [power s hs,power 2 (by norm_num),← Real.exp_add,Real.exp_le_exp]
  dsimp only [d] at cmp
  linarith

/-- If a sequence u is o(2^j) but exceeds faster geometric sequences than r^j,
the gaps 2 u_j - u_(j+1) exceed every fixed multiple of r^j arbitrarily late. -/
theorem big_gaps (u : ℕ → ℝ) {r : ℝ} (hr : 0<r) (r2 : r<2)
    (zero : Tendsto (fun j => u j/(2:ℝ)^j) atTop (𝓝 0))
    (large : ∀ C : ℝ, ∀ J : ℕ, ∃ j ≥ J, C*r^j < u j)
    (C : ℝ) (C0 : 0 ≤ C) (J : ℕ) :
    ∃ j ≥ J, C*r^j < 2*u j-u (j+1) := by
  by_contra! h
  let D := C/(2-r)
  have dd : D*(2-r)=C := div_mul_cancel₀ _ (by linarith)
  have nn : 0 ≤ D := div_nonneg C0 (by linarith)
  obtain ⟨a,aj,ha⟩ := large D J
  let v := fun j => u j-D*r^j
  have step {j : ℕ} (hj : J≤j) : 2*v j ≤ v (j+1) := by
    have b := h j hj
    have p := congrArg (fun x:ℝ => x*r^j) dd
    dsimp [v]
    rw [pow_succ]
    nlinarith only [b,p]
  have iter (t : ℕ) : (2:ℝ)^t*v a ≤ v (a+t) := by
    induction t with
    | zero => simp
    | succ t ih =>
      calc _ = 2*((2:ℝ)^t*v a) := by rw [pow_succ]; ring
           _ ≤ 2*v (a+t) := by linarith
           _ ≤ _ := step (by omega)
  have vp : 0<v a := sub_pos.mpr ha
  let c := v a/(2:ℝ)^a
  have cp : 0<c := div_pos vp (by positivity)
  have ev := (Metric.tendsto_nhds.mp zero) c cp
  obtain ⟨b,hb⟩ := eventually_atTop.mp ev
  have small := hb (a+b) (by omega)
  rw [Real.dist_eq,sub_zero] at small
  have up := (abs_lt.mp small).2
  have it := iter b
  have vw : v (a+b)≤u (a+b) := sub_le_self _ (mul_nonneg nn (pow_nonneg hr.le _))
  have low : c ≤ u (a+b)/(2:ℝ)^(a+b) := by
    dsimp [c]
    rw [div_le_div_iff₀ (by positivity) (by positivity),pow_add]
    have h' := mul_le_mul_of_nonneg_right (it.trans vw) (pow_nonneg (by norm_num : (0:ℝ)≤2) a)
    linarith only [h']
  linarith

theorem dyadic_gaps {k : ℕ} (hk : 3≤k) {r : ℝ} (hr : 0<r) (r2 : r<2)
    (zero : Tendsto (fun j => size k j/(2:ℝ)^j) atTop (𝓝 0))
    (C : ℝ) (C0 : 0≤C) (J : ℕ) :
    ∃ j ≥ J, C*r^j < gap k j := by
  apply big_gaps (size k) hr r2 zero _ C C0 J
  intro D L
  let s := (2+r)/2
  have sp : 0<s := by dsimp [s];linarith
  have sb : s<2 := by dsimp [s];linarith
  have sr : 1<s/r := (one_lt_div hr).mpr (by dsimp [s];linarith)
  have a := (tendsto_pow_atTop_atTop_of_one_lt sr).eventually (eventually_gt_atTop D)
  obtain ⟨j,he,hc,hj⟩ := (a.and ((capacity hk sp sb).and (eventually_ge_atTop L))).exists
  rw [div_pow] at he
  exact ⟨j,hj,((lt_div_iff₀ (pow_pos hr j)).mp he).trans_le hc⟩

theorem three_dyadic_gaps {r : ℝ} (hr : 0<r) (r2 : r<2)
    (C : ℝ) (C0 : 0≤C) (J : ℕ) :
    ∃ j ≥ J, C*r^j < gap 3 j :=
  dyadic_gaps (by decide) hr r2 roth_density_zero C C0 J

end Erdos142Loss
#print axioms Erdos142Loss.capacity
#print axioms Erdos142Loss.three_dyadic_gaps
