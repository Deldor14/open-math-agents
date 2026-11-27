import OMAStatements.S_oeis_a267921
import Mathlib

open OMA.S_oeis_a267921 PowerSeries
namespace Deldor14.Rule267921

private theorem truth (l c r : Bool) : rule l c r = (l || !c) := by
  cases l <;> cases c <;> cases r <;> decide

/-- At each positive time there is a single OFF cell, moving one place right. -/
private theorem singleOff (n : ℕ) (x : ℤ) : state (n+1) x = decide (x ≠ (n:ℤ)) := by
  induction n generalizing x with
  | zero =>
    simp only [state,step,initial,truth,Nat.cast_zero]
    by_cases h : x = 0 <;> simp [h] <;> omega
  | succ n ih =>
    change rule _ _ _ = _
    rw [truth]
    change (state (n+1) (x-1) || !(state (n+1) x)) = _
    rw [ih,ih]
    push_cast
    by_cases e : x = (n:ℤ)+1 <;> by_cases f : x = n <;>
      simp [e,f,show (x-1=n) ↔ x=(n:ℤ)+1 by omega]

private def rep : ℕ → ℕ
  | 0 => 0
  | n+1 => 2 * rep n+1

private theorem prefixOn (g : Row) (left : ℤ) (m : ℕ)
    (h : ∀ j : ℕ,j < m → g (left+j)=true) : encode g left m = rep m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [encode,ih (fun j hj => h j (by omega)),h m (by omega)]
    rfl

private theorem digits (n : ℕ) : a (n+1)=4*rep (2*n+1)+1 := by
  have firstDigits : encode (state (n+1)) (-((n+1:ℕ):ℤ)) (2*n+1) = rep (2*n+1) := by
    apply prefixOn
    intro j hj
    simp only [singleOff,decide_eq_true_eq]; omega
  unfold a
  rw [show 2*(n+1)+1=(2*n+1+1)+1 by omega,encode,encode,firstDigits]
  simp only [singleOff,bit,decide_eq_true_eq]
  rw [if_pos (by omega : -((n+1:ℕ):ℤ)+((2*n+1+1:ℕ):ℤ) ≠ (n:ℤ)),
    if_neg (by omega : ¬ (-((n+1:ℕ):ℤ)+((2*n+1:ℕ):ℤ) ≠ (n:ℤ)))] <;> ring

private theorem affine (n : ℕ) : (a (n+2):ℤ)=4*(a (n+1):ℤ)+9 := by
  rw [digits (n+1),digits n,show 2*(n+1)+1=(2*n+1+1)+1 by omega,rep,rep]
  push_cast
  ring

private theorem recurrence (n : ℕ) (hn : 2<n) :
    (a n:ℤ)=5*(a (n-1):ℤ)-4*(a (n-2):ℤ) := by
  obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
  change (a (k+3):ℤ)=5*(a (k+2):ℤ)-4*(a (k+1):ℤ)
  linarith [affine k,affine (k+1)]

private theorem generating : series*((1-X)*(1-4*X))=1+8*X^2 := by
  have left : series*((1-X)*(1-4*X))=
      series-((C (5:ℤ))*series)*X+((C (4:ℤ))*series)*X^2 := by simp only [map_ofNat]; ring
  have right : (1 + 8*X^2 : PowerSeries ℤ)=1+C (8:ℤ)*X^2 := by simp
  rw [left,right]
  apply PowerSeries.ext
  intro n
  have shift (f : PowerSeries ℤ) : coeff n (f*X) = if 1≤n then coeff (n-1) f else 0 := by
    simpa only [pow_one] using coeff_mul_X_pow' f 1 n
  simp only [map_add,map_sub,coeff_C_mul_X_pow,coeff_mul_X_pow',shift,coeff_C_mul,coeff_C,coeff_one,series,coeff_mk]
  by_cases hn : n<3
  · interval_cases n <;> norm_num [show a 0=1 by decide,show a 1=5 by decide,show a 2=29 by decide]
  · simp only [if_pos (by omega : 1≤n),if_pos (by omega : 2≤n),if_neg (by omega : n≠0),
      if_neg (by omega : n-2≠0)]
    linarith [recurrence n (by omega)]

end Deldor14.Rule267921
theorem OMA.solution : type_of% @OMA.S_oeis_a267921.main :=
  ⟨Deldor14.Rule267921.recurrence,Deldor14.Rule267921.generating⟩
