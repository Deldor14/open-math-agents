import RegularScales
import Mathlib

/-! Finite exceptional-window and density-transfer bounds for the local smoothness
condition in Morris–Ortega–Rué, Proposition 4.1 (arXiv:2607.17746).
The window length and threshold may vary with the final scale. -/
open Set.IsAPOfLengthFree ProgressionParity Finset
namespace Erdos142Windows

noncomputable def density (k n : ℕ) : ℝ := (maxCard k n:ℝ)/n

noncomputable def loss (k j : ℕ) : ℝ :=
  Real.log ((2:ℝ)^j)-Real.log (maxCard k (2^j))

private lemma pos (k n : ℕ) (hk : 3 ≤ k) (hn : 0<n) : 0<(maxCard k n:ℝ) := by
  have h:=interval_mono (by omega : 1<k) hn
  rw [(initial_values (by omega : 1<k)).1 1 (by omega)] at h
  exact_mod_cast (show 0 < maxCard k n by omega)

private lemma log_density (k j : ℕ) (hk : 3 ≤ k) :
    Real.log (density k (2^j)) = -loss k j := by
  unfold density loss
  rw [Real.log_div (pos k _ hk (by positivity)).ne' (by positivity)]
  push_cast
  ring

private lemma loss_mono (k : ℕ) (hk : 3 ≤ k) : Monotone (loss k) := by
  apply monotone_nat_of_le_succ
  intro j
  have bound := multiple_upper (by omega : 1<k) 2 (2^j)
  have b : (maxCard k (2^(j+1)):ℝ) ≤ 2*maxCard k (2^j) := by
    rw [pow_succ, Nat.mul_comm (2^j) 2];exact_mod_cast bound
  have e := Real.log_le_log (pos k _ hk (by positivity)) b
  rw [Real.log_mul (by norm_num) (pos k _ hk (by positivity)).ne'] at e
  unfold loss
  rw [pow_succ,Real.log_mul (by positivity) (by norm_num)]
  linarith

private theorem window_sum (F : ℕ → ℝ) (J w : ℕ) :
    ∑ j ∈ range J,(F (j+w)-F j) = ∑ i ∈ range w,(F (J+i)-F i) := by
  have left := sum_range_add (fun j => F j) J w
  have right := sum_range_add (fun j => F j) w J
  rw [Nat.add_comm w J] at right
  conv_rhs at right => enter [2, 2, x]; rw [Nat.add_comm w x]
  simp only [sum_sub_distrib]
  linarith

noncomputable def exceptional (k J w : ℕ) (τ : ℝ) : Finset ℕ := by
  classical exact (range J).filter fun j => τ ≤ loss k (j+w)-loss k j

/-- Total one-sided variation in translated windows. This controls the mean
error without first discarding endpoints at a fixed threshold. -/
theorem window_mass (k a J w : ℕ) (hk : 3 ≤ k) :
    ∑ j ∈ range J, (loss k (a+j+w)-loss k (a+j)) ≤
      (w:ℝ)*(loss k (a+J+w)-loss k a) := by
  have h := window_sum (fun j => loss k (a+j)) J w
  simp only [← Nat.add_assoc] at h
  rw [h]
  calc _ ≤ ∑ _i ∈ range w,(loss k (a+J+w)-loss k a) := by
         apply sum_le_sum
         intro i hi
         have hi' := mem_range.mp hi
         exact sub_le_sub (loss_mono k hk (by omega)) (loss_mono k hk (by omega))
       _ = _ := by simp [mul_sub]

/-- Unconditional finite bound; inserting a known density lower bound at a single
upper endpoint gives an exceptional-scale count. -/
theorem exceptional_bound (k J w : ℕ) (hk : 3 ≤ k) (τ : ℝ) :
    ((exceptional k J w τ).card:ℝ)*τ ≤ (w:ℝ)*loss k (J+w) := by
  classical
  have mono := loss_mono k hk
  have z : loss k 0=0 := by simp [loss,(initial_values (by omega : 1<k)).1 1 (by omega)]
  calc _ = ∑ _i ∈ exceptional k J w τ,τ := by simp
       _ ≤ ∑ j ∈ exceptional k J w τ,(loss k (j+w)-loss k j) :=
         sum_le_sum fun _ h => (mem_filter.mp h).2
       _ ≤ ∑ j ∈ range J,(loss k (j+w)-loss k j) :=
         sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sub_nonneg.mpr (mono (by omega)))
       _ = _ := window_sum _ J w
       _ ≤ ∑ _i ∈ range w,loss k (J+w) := by
         apply sum_le_sum
         intro i hi
         have h := mem_range.mp hi
         have lo := mono (Nat.zero_le i)
         have up := mono (show J+i≤J+w by omega)
         linarith
       _ = _ := by simp

/-- Block covering compares the density at arbitrary integer scales. -/
theorem density_cover {k u v : ℕ} (hk : 3 ≤ k) (hu : 0<u) (hv : 0<v) :
    density k u ≤ (1+(v:ℝ)/u)*density k v := by
  have md := Nat.mod_lt u hv
  have de := Nat.mod_add_div u v
  have fit : u ≤ (u/v+1)*v := by rw [Nat.succ_mul,Nat.mul_comm (u/v) v];omega
  have a := (interval_mono (by omega : 1<k) fit).trans (multiple_upper (by omega : 1<k) (u/v+1) v)
  have b : v*maxCard k u ≤ (u+v)*maxCard k v := by
    have e := Nat.mul_le_mul_left v a
    have l := Nat.div_mul_le_self u v
    calc _ ≤ v*((u/v+1)*maxCard k v) := e
         _ = ((u/v)*v+v)*maxCard k v := by ring
         _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have b' : (v:ℝ)*maxCard k u ≤ (u+v:ℝ)*maxCard k v := by exact_mod_cast b
  unfold density
  field_simp [show (u:ℝ)≠0 by positivity,show (v:ℝ)≠0 by positivity]
  nlinarith only [b']

/-- A good dyadic window implies the required one-sided density inequality at
every interior endpoint n; neither n nor the sampling length l must be dyadic. -/
theorem transfer {k j w n l : ℕ} (hk : 3 ≤ k) (hn : 0<n) (hl : 0<l)
    {a τ : ℝ} (ha : 0 ≤ a)
    (left : ((2^j:ℕ):ℝ)/l ≤ a) (right : (n:ℝ)/(2^(j+w):ℕ) ≤ a)
    (good : loss k (j+w)-loss k j ≤ τ) :
    Real.exp (-τ)*density k l ≤ (1+a)^2*density k n := by
  have A := density_cover hk hl (show 0<2^j by positivity)
  have B := density_cover hk (show 0<2^(j+w) by positivity) hn
  have non (x : ℕ) : 0 ≤ density k x := by unfold density;positivity
  have U := A.trans (mul_le_mul_of_nonneg_right (add_le_add_right left 1) (non _))
  have V := B.trans (mul_le_mul_of_nonneg_right (add_le_add_right right 1) (non _))
  have dpos (i : ℕ) : 0<density k (2^i) := div_pos (pos k _ hk (by positivity)) (by positivity)
  have e : Real.exp (-τ)*density k (2^j) ≤ density k (2^(j+w)) := by
    rw [← Real.log_le_log_iff (mul_pos (Real.exp_pos _) (dpos j)) (dpos (j+w)),
        Real.log_mul (Real.exp_pos _).ne' (dpos j).ne',Real.log_exp,log_density _ _ hk,log_density _ _ hk]
    linarith
  have p := mul_le_mul_of_nonneg_left U (Real.exp_pos (-τ)).le
  have q := mul_le_mul_of_nonneg_left (e.trans V) (show 0 ≤ 1+a by linarith)
  nlinarith only [p,q]

/-- Additive form used for hypothesis (9) in Proposition 4.1. -/
theorem smoothness {k j w n l : ℕ} (hk : 3 ≤ k) (hn : 0<n) (hl : 0<l)
    {a s : ℝ} (ha : 0 ≤ a)
    (left : ((2^j:ℕ):ℝ)/l ≤ a) (right : (n:ℝ)/(2^(j+w):ℕ) ≤ a)
    (good : loss k (j+w)-loss k j ≤ s) :
    (1-(s+2*a))*density k l ≤ density k n := by
  have b := transfer hk hn hl ha left right good
  have p : 0 < 1+a := by linarith
  have lpos : 0 ≤ density k l := by unfold density; positivity
  have lg : Real.log (1+a) ≤ a := by linarith [Real.log_le_sub_one_of_pos p]
  have x : Real.exp (-(s+2*a))*(1+a)^2 ≤ Real.exp (-s) := by
    rw [← Real.exp_log p, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
    push_cast
    linarith
  have y := Real.add_one_le_exp (-(s+2*a))
  have t := mul_le_mul_of_nonneg_right x lpos
  have u := mul_le_mul_of_nonneg_right y lpos
  have v : Real.exp (-(s+2*a))*density k l ≤ density k n := by
    apply le_of_mul_le_mul_left (a := (1+a)^2) _ (by positivity)
    nlinarith only [t,b]
  linarith
end Erdos142Windows
#print axioms Erdos142Windows.exceptional_bound
#print axioms Erdos142Windows.window_mass
#print axioms Erdos142Windows.transfer
#print axioms Erdos142Windows.smoothness
