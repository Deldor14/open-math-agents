import OMAStatements.S_oeis_a223299
import Mathlib

open OMA.S_oeis_a223299 PowerSeries
namespace Deldor14.GridRows

def count (n : ℕ) (r : Row) := (grids n r).length

theorem step (n : ℕ) (r : Row) : count (n+1) r=((after r).map (count n)).sum := by
  simp [count,grids,List.length_flatMap] <;> rfl

theorem total (n : ℕ) : a (n+1)=(rows.map (count n)).sum := by
  simp [a,count,List.length_flatMap] <;> rfl

theorem addRows (L : List Row) (f g h : Row → ℕ)
    (rel : ∀ x ∈ L, f x+12*g x=11*h x) :
    (L.map f).sum+12*(L.map g).sum=11*(L.map h).sum := by
  induction L with
  | nil => simp
  | cons r L ih =>
    have hr := rel r (by simp)
    have hs := ih (fun x hx => rel x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons]
    omega

set_option maxHeartbeats 2000000 in
theorem base : ∀ r ∈ rows, (after r |>.map fun s => (after s).length).sum + 12 = 11*(after r).length := by
  decide +kernel

theorem recurrence (n : ℕ) (r : Row) (hr : r ∈ rows) :
    count (n+2) r +12*count n r=11*count (n+1) r := by
  induction n generalizing r with
  | zero =>
    have o (s : Row) : count 1 s=(after s).length := by simp [step,count,grids,List.length_flatMap]
    rw [step 1,o]
    rw [show count 1 = (fun s => (after s).length) from funext o]
    exact base r hr
  | succ n ih =>
    rw [step (n+2),step n,step (n+1)]
    apply addRows
    intro x hx
    exact ih x (List.mem_filter.mp hx).1

theorem sequence (n : ℕ) : a (n+3)+12*a (n+1)=11*a (n+2) := by
  simpa only [total] using addRows rows (count (n+2)) (count n) (count (n+1)) (recurrence n)

theorem generating : (1-11*X+12*X^2)*(mk (fun n => (a n:ℚ)))=36*X*(1-2*X) := by
  let s : PowerSeries ℚ := mk fun n => (a n:ℚ)
  change _ * s = _
  have left : (1-11*X+12*X^2)*s=s-(C (11:ℚ)*s)*X+(C (12:ℚ)*s)*X^2 := by simp only [map_ofNat]; ring
  have right : 36*X*(1-2*X) = C (36:ℚ)*X^1 - C (72:ℚ)*X^2 := by simp only [map_ofNat]; ring
  rw [left,right]
  apply PowerSeries.ext
  intro n
  have shift (f : PowerSeries ℚ) : coeff n (f*X) = if 1≤n then coeff (n-1) f else 0 := by
    simpa only [pow_one] using coeff_mul_X_pow' f 1 n
  simp only [map_add,map_sub,coeff_C_mul_X_pow,coeff_mul_X_pow',shift,coeff_C_mul,s,coeff_mk]
  have a1 : a 1=36 := by decide +kernel
  have a2 : a 2=324 := by decide +kernel
  by_cases sm : n<3
  · interval_cases n <;> norm_num [a1,a2,show a 0=0 by rfl]
  · obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
    simp only [if_pos (by omega : 1≤k+3),if_pos (by omega : 2≤k+3),
      if_neg (by omega : k+3≠1),if_neg (by omega : k+3≠2),sub_zero,
      show k+3-1=k+2 by omega,show k+3-2=k+1 by omega]
    have rel : (a (k+3):ℚ)+12*a (k+1)=11*a (k+2) := by exact_mod_cast sequence k
    simp [coeff_C]
    linarith

theorem closedRec (n : ℕ) : closedValue (n+2) + 12*closedValue n=11*closedValue (n+1) := by
  let s := Real.sqrt 73
  have sq : s^2=73 := Real.sq_sqrt (by norm_num)
  let u := (11-s)/2
  let v := (11+s)/2
  have hu : u^2+12=11*u := by dsimp [u]; nlinarith
  have hv : v^2+12=11*v := by dsimp [v]; nlinarith
  change 3/s*((s-1)*u^(n+2)+(s+1)*v^(n+2)) + 12*(3/s*((s-1)*u^n+(s+1)*v^n)) =
    11*(3/s*((s-1)*u^(n+1)+(s+1)*v^(n+1)))
  rw [pow_add u n 2,pow_add v n 2,pow_succ,pow_succ]
  linear_combination (3/s)*(s-1)*u^n*hu + (3/s)*(s+1)*v^n*hv

set_option maxRecDepth 8192 in
theorem formula (n : ℕ) : (a (n+1):ℝ)=closedValue (n+1) := by
  have sq : (Real.sqrt 73)^2=73 := Real.sq_sqrt (by norm_num)
  have nz : Real.sqrt 73≠0 := by positivity
  induction n using Nat.twoStepInduction with
  | zero =>
    have h : a 1=36 := by decide +kernel
    rw [h]; unfold closedValue; norm_num; field_simp; ring
  | one =>
    have h : a 2=324 := by decide +kernel
    rw [h]; unfold closedValue; push_cast; field_simp [nz]; linear_combination (-6*Real.sqrt 73)*sq
  | more n h0 h1 =>
    have rel : (a (n+3):ℝ)+12*a (n+1)=11*a (n+2) := by exact_mod_cast sequence n
    rw [h0,h1] at rel
    linarith [closedRec (n+1)]

end Deldor14.GridRows
open Deldor14.GridRows

theorem OMA.solution : type_of% @OMA.S_oeis_a223299.main :=
  ⟨sequence,generating,formula⟩
