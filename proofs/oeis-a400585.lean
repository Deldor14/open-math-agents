import OMAStatements.S_oeis_a400585
import Mathlib

open OMA.S_oeis_a400585 Filter
open scoped Topology
namespace Deldor14.OddDivisors

private def block (n j : ℕ) : ℕ := if Odd j then (n/j+1).choose 3 else 0

private theorem cumulative (M n : ℕ) (hn : n<M) :
    ∑ k ∈ Finset.range (n+1),a k = ∑ j ∈ Finset.range M,block n j := by
  induction n with
  | zero => simp [a,block,Nat.choose]
  | succ n ih =>
    have divs : (n+1).divisors = (Finset.range M).filter (· ∣ n+1) := by
      ext j
      simp only [Nat.mem_divisors,Finset.mem_filter,Finset.mem_range]
      constructor
      · rintro ⟨d,_⟩
        exact ⟨lt_of_le_of_lt (Nat.le_of_dvd (by omega) d) hn,d⟩
      · rintro ⟨_,d⟩
        exact ⟨d,by omega⟩
    rw [Finset.sum_range_succ,ih (by omega),a,divs,Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases odd : Odd j
    · by_cases dvd : j ∣ n+1
      · simp only [block,if_pos odd,if_pos dvd,Nat.succ_div_of_dvd dvd]
        rw [Nat.choose_succ_succ' (n/j+1) 2,add_comm]
      · simp [block,odd,dvd,Nat.succ_div_of_not_dvd dvd]
    · simp [block,odd]

private noncomputable def w (j : ℕ) : ℝ := ((j:ℝ)^3)⁻¹
private noncomputable def normalized (n j : ℕ) : ℝ := (block n j:ℝ)/(n:ℝ)^3
private noncomputable def target (j : ℕ) : ℝ := if Odd j then w j/6 else 0

private theorem mass (n : ℕ) : ∑' j,normalized n j =
      (∑ k ∈ Finset.range (n+1),(a k:ℝ))/(n:ℝ)^3 := by
  rw [tsum_eq_sum (s := Finset.range (n+1))]
  · simp only [normalized,← Finset.sum_div]
    exact congrArg (fun z : ℝ => z/(n:ℝ)^3) (by exact_mod_cast (cumulative (n+1) n (by omega)).symm)
  · intro j hj
    have lt : n<j := by simpa using hj
    simp [normalized,block,Nat.div_eq_of_lt lt,Nat.choose]

private theorem cubic (q : ℕ) : 6*((q+1).choose 3:ℝ)=(q:ℝ)^3-q := by
  have first := Nat.add_one_mul_choose_eq q 2
  have second := Nat.choose_succ_right_eq q 1
  cases q with
  | zero => norm_num [Nat.choose]
  | succ k =>
    simp only [Nat.choose_one_right,Nat.add_sub_cancel] at second
    zify at first second
    push_cast
    exact_mod_cast (show (6:ℤ)*((k+1+1).choose 3:ℤ)=(k+1:ℤ)^3-(k+1:ℤ) by
      linear_combination -2*first+((k:ℤ)+2)*second)

private theorem ratio (j : ℕ) (hj : 0<j) :
    Tendsto (fun n : ℕ => ((n/j:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1/(j:ℝ))) := by
  have jp : 0<(j:ℝ) := by exact_mod_cast hj
  have grow : Tendsto (fun n : ℕ => (n:ℝ)/j) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const jp
  have lim := (tendsto_nat_floor_div_atTop.comp grow).div_const (j:ℝ)
  simpa only [Function.comp_def,Nat.floor_div_eq_div,div_div,div_mul_cancel₀ _ jp.ne'] using lim

private theorem pointwise (j : ℕ) : Tendsto (fun n => normalized n j) atTop (𝓝 (target j)) := by
  by_cases odd : Odd j
  · have hj : 0<j := by obtain ⟨k,e⟩ := odd;omega
    have hr := ratio j hj
    have inv : Tendsto (fun n : ℕ => (1:ℝ)/n) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    have lim := ((hr.pow 3).sub (hr.mul (inv.pow 2))).div_const 6
    apply Tendsto.congr' _ (by simpa [target,odd,w,one_div] using lim)
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have nc : (n:ℝ)≠0 := by positivity
    simp only [normalized,block,if_pos odd]
    field_simp
    nlinarith [cubic (n/j)]
  · simp [normalized,block,target,odd,tendsto_const_nhds]

private theorem bound (n j : ℕ) (hn : 0<n) : ‖normalized n j‖ ≤ w j := by
  by_cases odd : Odd j
  · have hj : 0<j := by obtain ⟨k,e⟩ := odd;omega
    have nj : (0:ℝ)<n := by positivity
    have jj : (0:ℝ)<j := by positivity
    have divle : (((n/j:ℕ):ℝ)*(j:ℝ)) ≤ (n:ℝ) := by exact_mod_cast Nat.div_mul_le_self n j
    have cap := pow_le_pow_left₀ (by positivity : 0 ≤ (((n/j:ℕ):ℝ)*(j:ℝ))) divle 3
    simp only [normalized,block,if_pos odd,Real.norm_eq_abs,w,← one_div]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ ((n/j+1).choose 3:ℝ)/(n:ℝ)^3)]
    apply (div_le_div_iff₀ (pow_pos nj 3) (pow_pos jj 3)).mpr
    have small : ((n/j+1).choose 3:ℝ) ≤ ((n/j:ℕ):ℝ)^3 := by
      nlinarith [cubic (n/j), show (0:ℝ)≤((n/j+1).choose 3:ℝ) by positivity]
    simpa [mul_pow] using (mul_le_mul_of_nonneg_right small (by positivity : 0 ≤ (j:ℝ)^3)).trans (by simpa [mul_pow] using cap)
  · simp [normalized,block,odd,w]

private theorem total : ∑' j,target j=7*zetaThree/48 := by
  have summ : Summable w := Real.summable_nat_pow_inv.mpr (by decide : 1<3)
  have evenSum := summ.comp_injective (show Function.Injective (fun n : ℕ => 2*n) by intro x y h;dsimp at h;omega)
  have oddSum := summ.comp_injective (show Function.Injective (fun n : ℕ => 2*n+1) by intro x y h;dsimp at h;omega)
  have split := tsum_even_add_odd evenSum oddSum
  have evenVal : ∑' n : ℕ,w (2*n)=zetaThree/8 := by
    unfold w zetaThree
    rw [← tsum_div_const]
    apply tsum_congr
    intro n
    push_cast
    ring_nf
  have getE (n : ℕ) : target (2*n)=0 := by
    simp [target,Nat.odd_iff]
  have getO (n : ℕ) : target (2*n+1)=w (2*n+1)/6 := by
    simp [target,Nat.odd_iff]
  have e : Summable (fun n : ℕ => target (2*n)) := by simp [getE]
  have o : Summable (fun n : ℕ => target (2*n+1)) := by
    apply Summable.of_nonneg_of_le (f := fun n : ℕ => w (2*n+1)) _ _ oddSum
    · intro n; rw [getO]; unfold w; positivity
    · intro n; rw [getO]; have pos : 0 ≤ w (2*n+1) := by unfold w; positivity
      linarith
  rw [← tsum_even_add_odd e o]
  simp only [getE,getO,tsum_zero,zero_add,tsum_div_const]
  change (∑' n : ℕ,w (2*n)) + (∑' n : ℕ,w (2*n+1)) = zetaThree at split
  linarith

theorem result : type_of% @OMA.S_oeis_a400585.main := by
  have h := tendsto_tsum_of_dominated_convergence
    (show Summable w from Real.summable_nat_pow_inv.mpr (by decide : 1<3)) pointwise
    (by filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn;exact fun j => bound n j hn)
  simpa only [mass,total] using h
end Deldor14.OddDivisors

theorem OMA.solution : type_of% @OMA.S_oeis_a400585.main := Deldor14.OddDivisors.result
