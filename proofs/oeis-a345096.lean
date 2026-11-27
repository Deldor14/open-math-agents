import OMAStatements.S_oeis_a345096
import Mathlib

open OMA.S_oeis_a345096 Finset Filter Real
open scoped Topology

namespace Deldor14.DivisorSum

theorem element (n k i : ℕ) (hk : 0 < k) :
    summand n k i = if k^i ∣ n then k else 1 := by
  let d := k^i
  have pos : 0 < d := pow_pos hk _
  change k ^ (1 - ⌈(n:ℚ)/d⌉ + ⌊(n:ℚ)/d⌋).toNat = if d ∣ n then k else 1
  by_cases h : d ∣ n
  · rcases h with ⟨t,ht⟩
    have q : (n:ℚ)/d = (t:ℚ) := (div_eq_iff (by positivity)).mpr (by exact_mod_cast ht.trans (Nat.mul_comm _ _))
    rw [q,if_pos (show d ∣ n from ⟨t,ht⟩)]
    simp
  · have no : (n:ℚ)/d ∉ Set.range Int.cast := by
      rintro ⟨z,hz⟩
      have e : (n:ℚ) = (d:ℚ)*z := by field_simp at hz; linarith
      have ez : (n:ℤ) = (d:ℤ)*z := by exact_mod_cast e
      exact h (Int.natCast_dvd_natCast.mp ⟨z,ez⟩)
    rw [if_neg h,(Int.ceil_eq_floor_add_one_iff_notMem _).mpr no]
    simp

theorem count (n : ℕ) (hn : 0 < n) : n.divisors.card ≤ 2*n.sqrt := by
  let s := Icc 1 n.sqrt
  have cover : n.divisors ⊆ s ∪ s.image (fun x => n/x) := by
    intro k hk
    have dv := Nat.dvd_of_mem_divisors hk
    have kp := Nat.pos_of_mem_divisors hk
    by_cases small : k ≤ n.sqrt
    · exact mem_union_left _ (mem_Icc.mpr ⟨kp,small⟩)
    · apply mem_union_right
      obtain ⟨t,ht⟩ := dv
      have tp : 0 < t := by
        cases t with
        | zero => simp_all
        | succ t => omega
      have ts : t ≤ n.sqrt := by
        by_contra! bad
        have b := Nat.mul_le_mul (show n.sqrt+1 ≤ k by omega) (show n.sqrt+1 ≤ t by omega)
        have c := Nat.lt_succ_sqrt n
        rw [← ht] at b
        exact (not_le_of_gt c) b
      refine mem_image.mpr ⟨t,mem_Icc.mpr ⟨tp,ts⟩,?_⟩
      rw [ht,Nat.mul_div_cancel _ tp]
  have h := (card_le_card cover).trans (card_union_le _ _)
  have c := card_image_le (s:=s) (f:=fun x => n/x)
  have hs : s.card=n.sqrt := by simp [s]
  omega

theorem linear_pow {k i : ℕ} (hk : 2 ≤ k) (hi : 1 ≤ i) : i*k ≤ k^i := by
  induction i,hi using Nat.le_induction with
  | base => simp
  | succ i hi ih =>
    rw [pow_succ]
    have prod := Nat.mul_le_mul_right k ih
    have ik : k ≤ i*k := by simpa using Nat.mul_le_mul_right k hi
    have twice := Nat.mul_le_mul_left (i*k) hk
    nlinarith

theorem row (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    k ≤ ∑ i ∈ Icc 1 k, summand n k i ∧
    (∑ i ∈ Icc 1 k, summand n k i) ≤ k + (if k∣n then n else 0) := by
  have base : (∑ i ∈ Icc 1 k, (1:ℕ)) = k := by simp
  constructor
  · calc
      k = ∑ i ∈ Icc 1 k, (1:ℕ) := base.symm
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        rw [element _ _ _ hk]
        split <;> omega
  · by_cases unit : k=1
    · subst k; simp [element]
    have bound (i : ℕ) (hi : i ∈ Icc 1 k) :
        summand n k i ≤ 1 + if k∣n ∧ i ≤ n/k then k else 0 := by
      have ip := (mem_Icc.mp hi).1
      rw [element _ _ _ hk]
      by_cases d : k^i ∣ n
      · have dk := (dvd_pow_self k (by omega : i ≠ 0)).trans d
        have mult := (linear_pow (by omega : 2 ≤ k) ip).trans (Nat.le_of_dvd hn d)
        rw [if_pos d, if_pos ⟨dk,(Nat.le_div_iff_mul_le hk).mpr mult⟩]
        omega
      · rw [if_neg d]; omega
    calc
      _ ≤ ∑ i ∈ Icc 1 k, (1 + if k∣n ∧ i ≤ n/k then k else 0) := sum_le_sum bound
      _ = k + ∑ i ∈ Icc 1 k, (if k∣n ∧ i ≤ n/k then k else 0) := by rw [sum_add_distrib,base]
      _ ≤ _ := by
        apply Nat.add_le_add_left
        split_ifs with h
        · simp only [h,true_and,← sum_filter, sum_const, nsmul_eq_mul]
          have sub : (Icc 1 k).filter (fun i => i ≤ n/k) ⊆ Icc 1 (n/k) := by
            intro i hi
            obtain ⟨h1,h2⟩ := mem_filter.mp hi
            exact mem_Icc.mpr ⟨(mem_Icc.mp h1).1,h2⟩
          have hc : ((Icc 1 k).filter (fun i => i ≤ n/k)).card ≤ n/k := by
            simpa using card_le_card sub
          exact (Nat.mul_le_mul_right k hc).trans (Nat.div_mul_le_self _ _)
        · simp [h]

theorem bound (n : ℕ) (hn : 0 < n) :
    n*(n+1) ≤ 2*value n ∧ 2*value n ≤ n*(n+1)+4*n.sqrt*n := by
  have tri : 2*(∑ k ∈ Icc 1 n,k) = n*(n+1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_Icc_succ_top (by omega)]
      have t : 2*(∑ k ∈ Icc 1 n,k)=n*(n+1) := by
        by_cases h : n=0
        · subst n; simp
        · exact ih (by omega)
      nlinarith
  have low := sum_le_sum (s:=Icc 1 n) (fun k hk => (row n k hn (mem_Icc.mp hk).1).1)
  have high := sum_le_sum (s:=Icc 1 n) (fun k hk => (row n k hn (mem_Icc.mp hk).1).2)
  have ds : (Icc 1 n).filter (fun k => k∣n)=n.divisors := by
    ext k
    simp only [mem_filter,mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨_,d⟩; exact ⟨d,hn.ne'⟩
    · rintro ⟨d,_⟩; exact ⟨⟨Nat.pos_of_dvd_of_pos d hn,Nat.le_of_dvd hn d⟩,d⟩
  rw [sum_add_distrib,←sum_filter,ds,sum_const,nsmul_eq_mul] at high
  have ct := Nat.mul_le_mul_right n (count n hn)
  unfold value
  constructor <;> nlinarith

end Deldor14.DivisorSum
open Deldor14.DivisorSum

theorem OMA.solution : type_of% @OMA.S_oeis_a345096.main := by
  have natTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have inv : Tendsto (fun n : ℕ => (1:ℝ)/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have small : Tendsto (fun n : ℕ => (1:ℝ)/Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp natTop)
  have right : Tendsto (fun n : ℕ => (1/2:ℝ) + (1/(n:ℝ))/2 + 2*(1/Real.sqrt n)) atTop (𝓝 (1/2)) := by
    simpa using ((tendsto_const_nhds (x:=(1/2:ℝ))).add (inv.div_const 2)).add (small.const_mul 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds right
  all_goals filter_upwards [eventually_ge_atTop 1] with n hn
  all_goals have hpos : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  all_goals obtain ⟨lo,hi⟩ := bound n hn
  · have r : (n:ℝ)*((n:ℝ)+1) ≤ 2*(value n:ℝ) := by exact_mod_cast lo
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  · have r : 2*(value n:ℝ) ≤ (n:ℝ)*((n:ℝ)+1)+4*(n.sqrt:ℝ)*n := by exact_mod_cast hi
    have hs : (n.sqrt:ℝ) ≤ Real.sqrt n := by
      apply Real.le_sqrt_of_sq_le
      exact_mod_cast Nat.sqrt_le' n
    rw [← Real.sqrt_div_self']
    apply (div_le_iff₀ (by positivity)).mpr
    field_simp [hpos.ne']
    nlinarith [mul_le_mul_of_nonneg_right hs hpos.le]
