import OMAStatements.S_oeis_a123341
import Mathlib

open Finset Filter Real OMA.S_oeis_a123341
open scoped Topology

namespace Deldor14.PrimeWindow

theorem prime_increment (n : ℕ) : (n+1).primeCounting ≤ n.primeCounting+1 := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_succ]
  split <;> omega

theorem prime_small {n : ℕ} (h : 1 ≤ n) : n.primeCounting < n := by
  induction n, h using Nat.le_induction with
  | base => decide +kernel
  | succ n _ ih => have := prime_increment n; omega

theorem recurrence {n : ℕ} (hn : 2 ≤ n) : a n = ∑ i ∈ range n.primeCounting, a (n-(i+1)) := by
  rw [a.eq_def, dif_neg (by omega : ¬n≤1)]

theorem positive {n : ℕ} (pos : 1≤n) : 0<a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases one : n=1
    · subst n; rw [a.eq_def]; decide
    · have kpos : 0 < n.primeCounting := by
        by_contra! h
        have := Nat.primeCounting_eq_zero_iff.mp (show n.primeCounting=0 by omega)
        omega
      have bound := Finset.single_le_sum (f:=fun i => a (n-(i+1))) (fun i _ => Nat.zero_le _)
        (Finset.mem_range.mpr kpos)
      rw [recurrence (by omega)]
      exact lt_of_lt_of_le (ih (n-(0+1)) (by omega) (by omega)) bound

noncomputable def weight (n : ℕ) : ℝ := (a n:ℝ)/2^n

theorem double_upper (n : ℕ) (hn : 1 ≤ n) : a (n+1)≤2*a n := by
  by_cases one : n=1
  · subst n; decide +kernel
  obtain ⟨t,ht⟩ : ∃ t, (n+1).primeCounting=t+1 := by
    have : (n+1).primeCounting ≠ 0 := fun z => by have := Nat.primeCounting_eq_zero_iff.mp z; omega
    exact ⟨(n+1).primeCounting-1,by omega⟩
  have step := prime_increment n
  have cut : (∑ i ∈ range t, a (n-(i+1))) ≤ ∑ i ∈ range n.primeCounting, a (n-(i+1)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (by intros; omega)
  rw [← recurrence (by omega)] at cut
  rw [recurrence (by omega),ht,Finset.sum_range_succ']
  simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero] at *
  omega

theorem weights_down : Antitone (fun n => weight (n+1)) := by
  apply antitone_nat_of_succ_le
  intro n
  have h : (a ((n+1)+1):ℝ) ≤ 2*(a (n+1):ℝ) := by exact_mod_cast double_upper (n+1) (by omega)
  unfold weight
  rw [pow_succ (2:ℝ) (n+1)]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right h (show 0 ≤ (2:ℝ)^(n+1) by positivity)]

theorem comparison {n m : ℕ} (hn : 1≤n) (hm : n ≤ m) : weight m ≤ weight n := by
  have h := weights_down (show n-1 ≤ m-1 by omega)
  simpa only [Nat.sub_add_cancel hn,Nat.sub_add_cancel (hn.trans hm)] using h

theorem sum_mass (k : ℕ) : (∑ i ∈ range k, (1/2:ℝ)^(i+1)) = 1-(1/2:ℝ)^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring

theorem weighted_recurrence {n : ℕ} (hn : 2≤n) :
    weight n = ∑ i ∈ range n.primeCounting, weight (n-(i+1))*(1/2:ℝ)^(i+1) := by
  have small := prime_small (show 1≤n by omega)
  unfold weight
  rw [recurrence hn,Nat.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i mem
  have hi := Finset.mem_range.mp mem
  have ex : n-(i+1)+(i+1)=n := by omega
  have p : (2:ℝ)^(n-(i+1))*2^(i+1)=2^n := by rw [← pow_add,ex]
  rw [one_div,inv_pow,div_eq_mul_inv,← p,mul_inv_rev]
  ring

theorem weight_lower {n : ℕ} (hn : 2≤n) :
    weight (n-1)*(1-(1/2:ℝ)^n.primeCounting) ≤ weight n := by
  rw [← sum_mass,Finset.mul_sum,weighted_recurrence hn]
  apply Finset.sum_le_sum
  intro i hi
  have small := prime_small (show 1≤n by omega)
  have mem := mem_range.mp hi
  exact mul_le_mul_of_nonneg_right (comparison (by omega) (by omega)) (by positivity)

theorem power_growth (k : ℕ) (hk : 10≤k) : 3*k*k+k+1 ≤ 2^k := by
  induction k,hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ]
    have t := Nat.mul_le_mul_right k hk
    nlinarith

theorem count_dyadic (k : ℕ) (hk : 10≤k) : 3*k ≤ (2^k).primeCounting := by
  have base := Chebyshev.pi_ge (2^k)
  have pos : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hi : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  have kl : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
  push_cast at base
  rw [Real.log_pow] at base
  have lower := (div_le_iff₀ (mul_pos kl pos)).mp base
  have near : Real.log ((2:ℝ)^k+1) ≤ ((k:ℝ)+1)*Real.log 2 := by
    calc _ ≤ Real.log ((2:ℝ)^(k+1)) := Real.log_le_log (by positivity) (by rw [pow_succ]; linarith)
         _ = _ := by rw [Real.log_pow]; push_cast; rfl
  have bound : (3*(k:ℝ)*k+k+1) ≤ (2:ℝ)^k := by exact_mod_cast power_growth k hk
  have mulBound := mul_le_mul_of_nonneg_right bound pos.le
  by_contra! few
  have fewR : (((2^k).primeCounting:ℕ):ℝ)<3*(k:ℝ) := by exact_mod_cast few
  nlinarith [mul_lt_mul_of_pos_right fewR (mul_pos kl pos)]

theorem count_controls_square {n : ℕ} (hn : 1024≤n) : n^2 ≤ 2^n.primeCounting := by
  obtain ⟨k,lo,hi⟩ := exists_nat_pow_near (by omega : 1≤n) (by decide : 1<(2:ℕ))
  have hk : 10≤k := by
    by_contra! bad
    have edge := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show k+1≤10 by omega)
    omega
  have bound := (count_dyadic k hk).trans (Nat.monotone_primeCounting lo)
  calc
    n^2 ≤ ((2:ℕ)^(k+1))^2 := Nat.pow_le_pow_left hi.le 2
    _ = 2^((k+1)*2) := (pow_mul _ _ _).symm
    _ ≤ 2^n.primeCounting := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega)

noncomputable def protectedWeight (n : ℕ) : ℝ := weight n * n / ((n:ℝ)+1)

theorem protected_up (n : ℕ) (hn : 1024≤n) : protectedWeight n ≤ protectedWeight (n+1) := by
  have count := count_controls_square (show 1024≤n+1 by omega)
  have bound : ((n:ℝ)+1)^2 ≤ 2^(n+1).primeCounting := by exact_mod_cast count
  have den : 0 < (2:ℝ)^(n+1).primeCounting := by positivity
  have inv : (1/2:ℝ)^(n+1).primeCounting ≤ 1/((n:ℝ)+1)^2 := by
    rw [one_div,inv_pow,← one_div]
    exact one_div_le_one_div_of_le (by positivity) bound
  have low := weight_lower (n:=n+1) (by omega)
  simp only [Nat.add_one_sub_one] at low
  have nonneg : 0≤weight n := by unfold weight; positivity
  have h : weight n*(1-1/((n:ℝ)+1)^2) ≤ weight (n+1) :=
    (mul_le_mul_of_nonneg_left (by linarith) nonneg).trans low
  unfold protectedWeight
  push_cast
  field_simp at h ⊢
  nlinarith

theorem uniform {n : ℕ} (hn : 1024≤n) : protectedWeight 1024 ≤ weight n := by
  have mono : protectedWeight 1024 ≤ protectedWeight n := by
    induction n,hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => exact ih.trans (protected_up n hn)
  apply mono.trans
  unfold protectedWeight
  apply (div_le_iff₀ (by positivity)).mpr
  have : 0≤weight n := by unfold weight; positivity
  nlinarith

end Deldor14.PrimeWindow
open Deldor14.PrimeWindow

theorem OMA.solution : type_of% @OMA.S_oeis_a123341.main := by
  let L := ⨅ n : ℕ, weight (n+1)
  have nonneg : ∀ n, 0≤weight n := fun n => by unfold weight; positivity
  have conv : Tendsto weight atTop (𝓝 L) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    exact tendsto_atTop_ciInf weights_down ⟨0,by rintro _ ⟨n,rfl⟩; exact nonneg _⟩
  have h : 0<protectedWeight 1024 := by
    have pos : 0<(a 1024:ℝ) := by exact_mod_cast positive (n:=1024) (by decide)
    unfold protectedWeight weight; positivity
  exact ⟨L,h.trans_le (ge_of_tendsto conv (eventually_atTop.mpr ⟨1024,fun _ hn => uniform hn⟩)),conv⟩
