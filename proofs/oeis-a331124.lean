import OMAStatements.S_oeis_a331124
import Mathlib

/-! The subsequence with six alternating binary digits appended at every
step grows by at least 257, while the power 4/3 allows a factor of 256. -/
namespace Deldor14.FibonacciCalls
open OMA.S_oeis_a331124 Filter
private def vec (t : ℕ) : Fin 4 → ℕ := ![calls t,calls (t+1),calls (t+2),calls (t+3)]
private def z (w : Fin 4 → ℕ) : Fin 4 → ℕ := ![w 0+w 1,w 0+w 1+w 2,w 1+w 2,w 1+w 2+w 3]
private def o (w : Fin 4 → ℕ) : Fin 4 → ℕ := ![w 0+w 1+w 2,w 1+w 2,w 1+w 2+w 3,w 2+w 3]
private lemma rec1 (t : ℕ) (ht : 2 ≤ t) : calls (2*t+1)=1+calls t+calls (t+1) := by
  rw [calls, dif_neg (by omega), if_neg (by omega)]
  simp only [show (2*t+1)/2+1 = t+1 by omega, show (2*t+1)/2 = t by omega]
private lemma rec2 (t : ℕ) (ht : 2 ≤ t) : calls (2*t+2)=1+calls t+calls (t+1)+calls (t+2) := by
  rw [calls, dif_neg (by omega), if_pos (by omega)]
  simp only [show (2*t+2)/2-1 = t by omega, show (2*t+2)/2+1 = t+2 by omega, show (2*t+2)/2 = t+1 by omega]
  rw [show t+1-1=t by omega]
private lemma rec3 (t : ℕ) (ht : 2 ≤ t) : calls (2*t+3)=1+calls (t+1)+calls (t+2) := by
  rw [calls, dif_neg (by omega), if_neg (by omega)]
  simp only [show (2*t+3)/2+1 = t+2 by omega, show (2*t+3)/2 = t+1 by omega]
private lemma rec4 (t : ℕ) (ht : 2 ≤ t) : calls (2*t+4)=1+calls (t+1)+calls (t+2)+calls (t+3) := by
  rw [calls, dif_neg (by omega), if_pos (by omega)]
  simp only [show (2*t+4)/2-1 = t+1 by omega, show (2*t+4)/2+1 = t+3 by omega, show (2*t+4)/2 = t+2 by omega]
  rw [show t+2-1=t+1 by omega]
private lemma rec5 (t : ℕ) (ht : 2 ≤ t) : calls (2*t+5)=1+calls (t+2)+calls (t+3) := by
  rw [calls, dif_neg (by omega), if_neg (by omega)]
  simp only [show (2*t+5)/2+1 = t+3 by omega, show (2*t+5)/2 = t+2 by omega]
private lemma lift_z (t : ℕ) (ht : 2 ≤ t) (w : Fin 4 → ℕ) (h : w ≤ vec t) :
    z w ≤ vec (2*t+1) := by
  have a := h 0;have b := h 1;have c := h 2;have d := h 3
  simp [vec] at a b c d
  intro i
  fin_cases i <;> simp [z,vec,rec1 t ht,rec2 t ht,rec3 t ht,rec4 t ht] <;> omega
private lemma lift_o (t : ℕ) (ht : 2 ≤ t) (w : Fin 4 → ℕ) (h : w ≤ vec t) :
    o w ≤ vec (2*t+2) := by
  have a := h 0;have b := h 1;have c := h 2;have d := h 3
  simp [vec] at a b c d
  intro i
  fin_cases i <;> simp [o,vec,rec2 t ht,rec3 t ht,rec4 t ht,rec5 t ht] <;> omega
private def seed : Fin 4 → ℕ := ![5,4,6,3]
private def idx : ℕ → ℕ | 0 => 4 | k+1 => 64*idx k+84
private lemma size (k : ℕ) : k ≤ idx k ∧ 2 ≤ idx k ∧ idx k+2 ≤ 6*64^k := by
  induction k with
  | zero => decide
  | succ k ih => rw [idx,pow_succ];omega
private lemma growth (k : ℕ) : (fun i => 257^k*seed i) ≤ vec (idx k) := by
  induction k with
  | zero =>
    have b0 : calls 0=1 := by rw [calls];norm_num
    have b1 : calls 1=1 := by rw [calls];norm_num [b0]
    have b2 : calls 2=1 := by rw [calls];norm_num [b0,b1]
    have b3 : calls 3=3 := by rw [calls];norm_num [b0,b1,b2]
    have b4 : calls 4=6 := by rw [calls];norm_num [b0,b1,b2,b3]
    have b5 : calls 5=5 := by rw [calls];norm_num [b0,b1,b2,b3,b4]
    have b6 : calls 6=11 := by rw [calls];norm_num [b0,b1,b2,b3,b4,b5]
    have b7 : calls 7=10 := by rw [calls];norm_num [b0,b1,b2,b3,b4,b5,b6]
    intro i;fin_cases i <;> norm_num [vec,idx,seed,b4,b5,b6,b7]
  | succ k ih =>
    let t:=idx k
    have ht : 2 ≤ t := (size k).2.1
    let w (i : Fin 4) := 257^k*seed i
    have h1 := lift_z t ht w ih
    have h2 := lift_o _ (by omega) _ h1
    have h3 := lift_z _ (by omega) _ h2
    have h4 := lift_o _ (by omega) _ h3
    have h5 := lift_z _ (by omega) _ h4
    have h6 := lift_o _ (by omega) _ h5
    change o (z (o (z (o (z w))))) ≤ vec (2*(2*(2*(2*(2*(2*t+1)+2)+1)+2)+1)+2) at h6
    rw [show 2*(2*(2*(2*(2*(2*t+1)+2)+1)+2)+1)+2=64*t+84 by ring] at h6
    change _ ≤ vec (64*t+84)
    apply le_trans _ h6
    intro i; fin_cases i <;> simp [w,seed,z,o,pow_succ] <;> omega
private lemma envelope (k : ℕ) : (idx k : ℝ)^((4:ℝ)/3) ≤ 16*256^k := by
  have e := (size k).2.2
  have en : idx k ≤ (2*4^k)^3 := by
    rw [mul_pow,←pow_mul, Nat.mul_comm k 3,pow_mul]
    norm_num;omega
  have er : (idx k:ℝ) ≤ ((2:ℝ)*4^k)^3 := by exact_mod_cast en
  calc
    _ ≤ (((2:ℝ)*4^k)^3)^((4:ℝ)/3) := Real.rpow_le_rpow (by positivity) er (by norm_num)
    _ = ((2:ℝ)*4^k)^((3:ℝ)*(4/3)) := (Real.rpow_natCast_mul (by positivity) 3 _).symm
    _ = ((2:ℝ)*4^k)^4 := by norm_num
    _ = _ := by rw [mul_pow,←pow_mul,Nat.mul_comm k 4,pow_mul];norm_num

theorem refute : ¬ (type_of% @OMA.S_oeis_a331124.main) := by
  rintro ⟨C,hC,N,claim⟩
  have grows := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<257/256)
  obtain ⟨k,big,high⟩ := ((eventually_ge_atTop N).and (grows.eventually_gt_atTop (16*C))).exists
  have lower : 257^k ≤ calls (idx k) := by
    have e := growth k 0
    simp [seed,vec] at e;omega
  have bound := claim (idx k) (big.trans (size k).1)
  have u := mul_le_mul_of_nonneg_left (envelope k) hC.le
  rw [div_pow] at high
  have final := (lt_div_iff₀ (by positivity)).mp high
  have low : (257:ℝ)^k ≤ calls (idx k) := by exact_mod_cast lower
  nlinarith
end Deldor14.FibonacciCalls
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a331124.main) := Deldor14.FibonacciCalls.refute
