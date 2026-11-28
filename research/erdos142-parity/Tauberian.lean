import Mathlib
import LocalGrowth

/-! Uniform, two-sided finite difference bounds for two monotone sequences.
The error at all three endpoints is expressed relative to the reference primitive. -/
open Finset
namespace Erdos142Means

def partialSum (u : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, u i

theorem prefix_le (u : ℕ → ℝ) (hu : Monotone u) (n : ℕ) :
    partialSum u n ≤ n * u n := by
  calc partialSum u n ≤ ∑ _i ∈ range n, u n := sum_le_sum fun i hi => hu (mem_range.mp hi).le
       _ = _ := by simp

theorem right_slope {u : ℕ → ℝ} (hu : Monotone u) (n h : ℕ) :
    (h:ℝ) * u n ≤ partialSum u (n+h)-partialSum u n ∧
      partialSum u (n+h)-partialSum u n ≤ (h:ℝ)*u (n+h) := by
  have s : partialSum u (n+h)-partialSum u n = ∑ j ∈ range h, u (n+j) := by
    simp only [partialSum,sum_range_add,add_sub_cancel_left]
  rw [s]
  constructor
  · calc _ = ∑ _j ∈ range h, u n := by simp
         _ ≤ _ := sum_le_sum fun j _ => hu (by omega)
  · calc _ ≤ ∑ _j ∈ range h, u (n+h) := sum_le_sum fun j hj => hu (by have := mem_range.mp hj;omega)
         _ = _ := by simp

theorem centered {f u : ℕ → ℝ} (hf : Monotone f) (hu : Monotone u)
    {n h : ℕ} (fits : h ≤ n) {E : ℝ}
    (left : |partialSum f (n-h)-partialSum u (n-h)| ≤ E)
    (mid : |partialSum f n-partialSum u n| ≤ E)
    (right : |partialSum f (n+h)-partialSum u (n+h)| ≤ E) :
    (h:ℝ)*(u (n-h)-f n) ≤ 2*E ∧ (h:ℝ)*(f n-u (n+h)) ≤ 2*E := by
  have a := (right_slope hf (n-h) h).2
  have b := (right_slope hu (n-h) h).1
  rw [Nat.sub_add_cancel fits] at a b
  have c := (right_slope hf n h).1
  have d := (right_slope hu n h).2
  rcases abs_le.mp left with ⟨l₁,l₂⟩
  rcases abs_le.mp mid with ⟨m₁,m₂⟩
  rcases abs_le.mp right with ⟨r₁,r₂⟩
  constructor <;> linarith

/-- In a multiplicative window, a small relative error for the two primitive sums
controls the relative error of point values, with no derivative of f assumed. -/
theorem recover {f u : ℕ → ℝ} (hf : Monotone f) (hu : Monotone u)
    {N h B : ℕ} (hh : 0 < h) (hN : h ≤ N) (scale : N ≤ B*h)
    {η δ : ℝ} (ed : 0 ≤ δ) (pos : 0 < u N)
    (localLo : (1-η)*u N ≤ u (N-h))
    (localHi : u (N+h) ≤ (1+η)*u N) (dbl : u (N+h) ≤ 2*u N)
    (err : ∀ j, N-h ≤ j → j ≤ N+h → |partialSum f j-partialSum u j| ≤ δ*partialSum u j) :
    |f N / u N-1| ≤ η+8*B*δ := by
  have bound (j : ℕ) (lo : N-h ≤ j) (hi : j ≤ N+h) :
      |partialSum f j-partialSum u j| ≤ δ*(4*N*u N) := by
    have ju : u j ≤ 2*u N := (hu hi).trans dbl
    have jN : (j:ℝ) ≤ 2*N := by exact_mod_cast (show j ≤ 2*N by omega)
    have q : (j:ℝ)*u j ≤ (2*N)*(2*u N) := mul_le_mul ju jN (by positivity) (by positivity) |> fun v => by simpa [mul_comm] using v
    exact (err j lo hi).trans (mul_le_mul_of_nonneg_left ((prefix_le u hu j).trans (by linarith)) ed)
  obtain ⟨lo,hi⟩ := centered hf hu hN (bound _ le_rfl (by omega)) (bound _ (by omega) (by omega)) (bound _ (by omega) le_rfl)
  have scaleR : (N:ℝ) ≤ B*h := by exact_mod_cast scale
  have hp : (0:ℝ)<h := by exact_mod_cast hh
  have ce : 2*(δ*(4*N*u N)) ≤ (h:ℝ)*(8*B*δ*u N) := by
    have e := mul_le_mul_of_nonneg_right scaleR (show 0 ≤ 8*δ*u N by positivity)
    linarith
  have lo' : u (N-h)-f N ≤ 8*B*δ*u N := le_of_mul_le_mul_left (lo.trans ce) hp
  have hi' : f N-u (N+h) ≤ 8*B*δ*u N := le_of_mul_le_mul_left (hi.trans ce) hp
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le,le_div_iff₀ pos]
    linarith
  · rw [sub_le_iff_le_add,div_le_iff₀ pos]
    linarith

end Erdos142Means

/-! A rate-free Tauberian implication for the exact extremal function in Erdős 142.
A nondecreasing candidate is determined to relative error o(1) by its own primitive
if that primitive agrees to relative error o(1) with the primitive of the extremal function. -/
open Finset Filter Set.IsAPOfLengthFree ProgressionParity
open scoped Topology
namespace Erdos142Means

noncomputable abbrev R (k n : ℕ) : ℝ := maxCard k n

private lemma monoR (k : ℕ) (hk : 3 ≤ k) : Monotone (R k) :=
  fun _ _ h => by exact_mod_cast interval_mono (by omega : 1<k) h

private lemma posR (k n : ℕ) (hk : 3 ≤ k) (hn : 0 < n) : 0 < R k n := by
  have e := (initial_values (by omega : 1<k)).1 1 (by omega)
  have b := interval_mono (by omega : 1<k) (show 1 ≤ n by omega)
  rw [e] at b
  exact_mod_cast (show 0 < maxCard k n by omega)

private lemma digit_capacity (i : ℕ) : i+1 ≤ maxCard 3 (3^i) := by
  induction i with
  | zero => simp [(initial_values (by decide : 1<3)).1 1 (by decide)]
  | succ i ih =>
    have e := digit_product (k:=3) (m:=2) (b:=3) (by decide) (by decide) (by decide) (3^i)
    rw [(initial_values (by decide : 1<3)).1 2 (by decide),mul_comm 3,← pow_succ] at e
    omega

private lemma local_increment {k m n h : ℕ} (hk : 3 ≤ k) (hm : 0 < m)
    (fits : (2*m-1)*h ≤ n) : (maxCard 3 m:ℝ) * (R k (n+h)-R k n) ≤ R k n := by
  have mono := interval_mono (by omega : 1<k) (show n ≤ n+h by omega)
  have bound := relative_increment hk hm fits
  have hr : (maxCard 3 m:ℝ) * ((maxCard k (n+h)-maxCard k n:ℕ):ℝ) ≤ (maxCard k n:ℝ) := by exact_mod_cast bound
  simpa only [R,Nat.cast_sub mono] using hr

private lemma local_pair {k t m N h : ℕ} (hk : 3 ≤ k) (ht : 0 < t) (hm : 0 < m)
    (capacity : t ≤ maxCard 3 m) (space : 2*m*h ≤ N) :
    (1-(t:ℝ)⁻¹)*R k N ≤ R k (N-h) ∧ R k (N+h) ≤ (1+(t:ℝ)⁻¹)*R k N := by
  have hle : h ≤ N := by nlinarith
  have eq : (2*m-1)*h+h=2*m*h := by
    rw [← Nat.succ_mul];congr 1;omega
  have a := local_increment hk hm (show (2*m-1)*h ≤ N-h by omega)
  rw [Nat.sub_add_cancel hle] at a
  have b := local_increment hk hm (show (2*m-1)*h ≤ N by omega)
  have left := monoR k hk (Nat.sub_le N h)
  have right := monoR k hk (show N ≤ N+h by omega)
  have tc : (t:ℝ) ≤ maxCard 3 m := by exact_mod_cast capacity
  have tp : (0:ℝ)<t := by exact_mod_cast ht
  have l := (mul_le_mul_of_nonneg_right tc (sub_nonneg.mpr left)).trans (a.trans left)
  have r := (mul_le_mul_of_nonneg_right tc (sub_nonneg.mpr right)).trans b
  have yl : R k N-R k (N-h) ≤ R k N/t := (le_div_iff₀ tp).mpr (by linarith)
  have yr : R k (N+h)-R k N ≤ R k N/t := (le_div_iff₀ tp).mpr (by linarith)
  rw [div_eq_mul_inv] at yl yr
  constructor <;> linarith

/-- Relative approximation of cumulative sums, at any rate, suffices for a monotone
candidate. No smoothness or regular variation of the candidate is required. -/
theorem from_primitive {k : ℕ} (hk : 3 ≤ k) {f : ℕ → ℝ} (hf : Monotone f)
    (approximation : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
       |partialSum f n-partialSum (R k) n| ≤ δ*partialSum (R k) n) :
    Tendsto (fun n => f n/R k n) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  obtain ⟨t,ht⟩ := exists_nat_gt (max 1 (2/ε))
  have ht1 : (1:ℝ)<t := (le_max_left _ _).trans_lt ht
  have ht0 : 0<t := by exact_mod_cast (zero_lt_one.trans ht1)
  have ht' : (t:ℝ)⁻¹ < ε/2 := by
    have b := (div_lt_iff₀ he).mp ((le_max_right _ _).trans_lt ht)
    rw [← one_div,div_lt_iff₀ (by positivity : (0:ℝ)<t)]
    linarith
  let m := 3^t
  have hm : 0 < m := by dsimp [m];positivity
  let B := 4*m
  let δ : ℝ := ε/(32*(B:ℝ))
  have bpos : 0 < B := by dsimp [B];omega
  have de : 0 < δ := by dsimp [δ];positivity
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (approximation δ de)
  filter_upwards [eventually_ge_atTop (max (2*m) (2*J+2))] with N hN
  let h := N/(2*m)
  have hn : 0 < h := Nat.div_pos (by omega) (by omega)
  have sp : 2*m*h ≤ N := Nat.mul_div_le _ _
  have hle : h ≤ N := by nlinarith
  have twoh : 2*h ≤ N := (Nat.mul_le_mul_right h (show 2 ≤ 2*m by omega)).trans sp
  have jle : J ≤ N-h := by omega
  have sc : N ≤ B*h := by
    have md := Nat.mod_lt N (show 0<2*m by omega)
    have rem := Nat.mod_add_div N (2*m)
    change N ≤ 4*m*h
    change N%(2*m)+2*m*h=N at rem
    nlinarith [Nat.mul_le_mul_left (2*m) (show 1 ≤ h by omega)]
  obtain ⟨lo,hi⟩ := local_pair hk ht0 hm (show t ≤ maxCard 3 m from (Nat.le_succ t).trans (digit_capacity t)) sp
  have p := posR k N hk (by omega)
  have one : (t:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1.le
  have dbl : R k (N+h) ≤ 2*R k N := hi.trans (mul_le_mul_of_nonneg_right (by linarith) p.le)
  have out := recover hf (monoR k hk) hn hle sc de.le p lo hi dbl (fun j lj _ => hJ j (jle.trans lj))
  rw [Real.dist_eq]
  apply out.trans_lt
  have cancel : 8*(B:ℝ)*δ=ε/4 := by dsimp [δ];field_simp;ring
  rw [cancel];linarith
end Erdos142Means

open Finset Filter Set.IsAPOfLengthFree ProgressionParity
open scoped Topology
namespace Erdos142Means

private lemma reference_grows (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (partialSum (R k)) atTop atTop := by
  have unit : R k 1 = 1 := by
    change ((maxCard k 1:ℕ):ℝ)=1
    rw [(initial_values (by omega : 1<k)).1 1 (by omega)]
    norm_num
  have lower (n : ℕ) : (n:ℝ) ≤ partialSum (R k) (n+1) := by
    induction n with
    | zero => simp [partialSum,R]
    | succ n ih =>
      have h : (1:ℝ) ≤ R k (n+1) := by
        rw [← unit];exact_mod_cast interval_mono (by omega : 1<k) (show 1 ≤ n+1 by omega)
      simp only [partialSum,sum_range_succ,Nat.cast_succ] at ih ⊢
      linarith
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨m,hm⟩ := exists_nat_gt b
  filter_upwards [eventually_ge_atTop (m+1)] with n hn
  have eq : n=(n-1)+1 := by omega
  have low := lower (n-1)
  rw [← eq] at low
  exact (hm.le.trans (by exact_mod_cast (show m ≤ n-1 by omega))).trans low

private lemma relative_of_ratio {a b : ℕ → ℝ} (hp : ∀ᶠ n in atTop, 0 < b n)
    (h : Tendsto (fun n => a n / b n) atTop (𝓝 1)) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ n in atTop, |a n-b n| ≤ ε*b n := by
  filter_upwards [Metric.tendsto_nhds.mp h ε he,hp] with n hn pos
  rw [Real.dist_eq,div_sub_one pos.ne',abs_div,abs_of_pos pos] at hn
  exact ((div_lt_iff₀ pos).mp hn).le

private lemma primitive_of_point {f u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n)
    (hp : ∀ᶠ n in atTop, 0 < u n) (growth : Tendsto (partialSum u) atTop atTop)
    (h : Tendsto (fun n => f n/u n) atTop (𝓝 1)) :
    Tendsto (fun n => partialSum f n/partialSum u n) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (relative_of_ratio hp h (show 0 < ε/3 by positivity))
  let C := |partialSum f J-partialSum u J|
  have bound (n : ℕ) : J ≤ n →
      |partialSum f n-partialSum u n| ≤ C+(ε/3)*partialSum u n := by
    intro hn
    induction n, hn using Nat.le_induction with
    | base =>
      have p : 0 ≤ partialSum u J := sum_nonneg fun i _ => hu i
      dsimp [C]
      nlinarith
    | succ n hn ih =>
      have addF : partialSum f (n+1)=partialSum f n+f n := sum_range_succ _ _
      have addU : partialSum u (n+1)=partialSum u n+u n := sum_range_succ _ _
      rw [addF,addU,show partialSum f n+f n-(partialSum u n+u n)=
         (partialSum f n-partialSum u n)+(f n-u n) by ring]
      exact (abs_add_le _ _).trans (by linarith [hJ n hn])
  filter_upwards [eventually_ge_atTop J,(tendsto_atTop.mp growth) (3*C/ε+1),
    (tendsto_atTop.mp growth) 1] with n hn scale pos
  have sp : 0 < partialSum u n := by linarith
  rw [Real.dist_eq,div_sub_one sp.ne',abs_div,abs_of_pos sp,div_lt_iff₀ sp]
  have c : 3*C/ε < partialSum u n := by linarith
  have sc := (div_lt_iff₀ he).mp c
  nlinarith [bound n hn]

/-- Rate-free equivalence with cumulative counts on the exact Erdős extremal function. -/
theorem primitive_ratio_iff {k : ℕ} (hk : 3 ≤ k) {f : ℕ → ℝ} (hf : Monotone f) :
    Tendsto (fun n => partialSum f n/partialSum (R k) n) atTop (𝓝 1) ↔
    Tendsto (fun n => f n/R k n) atTop (𝓝 1) := by
  have g := reference_grows k hk
  constructor
  · intro h
    exact from_primitive hk hf (fun _ he => relative_of_ratio (g.eventually_gt_atTop 0) h he)
  · intro h
    have e : ∀ᶠ n in atTop, 0 < R k n := by
      filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
      have h' := interval_mono (by omega : 1<k) hn
      rw [(initial_values (by omega : 1<k)).1 1 (by omega)] at h'
      exact_mod_cast (show 0 < maxCard k n by omega)
    exact primitive_of_point (fun n => Nat.cast_nonneg _) e g h
end Erdos142Means

#print axioms Erdos142Means.primitive_ratio_iff
