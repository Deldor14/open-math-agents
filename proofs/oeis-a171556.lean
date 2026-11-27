import OMAStatements.S_oeis_a171556
import Mathlib

open OMA.S_oeis_a171556
namespace Deldor14.Catalan

private theorem step (k : ℕ) : ((k:ℤ)+2)*catalan (k+1)=2*(2*k+1:ℤ)*catalan k := by
  have h := Nat.succ_mul_centralBinom_succ k
  rw [← succ_mul_catalan_eq_centralBinom,← succ_mul_catalan_eq_centralBinom] at h
  have h' : ((k:ℤ)+1)*(((k:ℤ)+2)*catalan (k+1)) =
      ((k:ℤ)+1)*(2*(2*k+1:ℤ)*catalan k) := by
    zify at h
    linear_combination h
  exact mul_left_cancel₀ (by positivity : (k:ℤ)+1≠0) h'

private theorem castA (k : ℕ) : (a k:ℤ)=3*(catalan k:ℤ)-2 := by
  have p : 0<catalan k := by
    have t := Nat.centralBinom_pos k
    rw [← succ_mul_catalan_eq_centralBinom] at t
    exact Nat.pos_of_mul_pos_left t
  simp [a,Nat.cast_sub (by omega : 2 ≤ 3*catalan k)]

theorem result : type_of% @OMA.S_oeis_a171556.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+2 := ⟨n-2,by omega⟩
  simp only [show k+2-1=k+1 by omega,Nat.add_sub_cancel,castA,Nat.cast_add,Nat.cast_ofNat]
  have h := step (k+1)
  simp only [Nat.cast_succ] at h
  linear_combination 3*(k:ℤ)*h-3*((k:ℤ)+1)*(step k)
end Deldor14.Catalan

theorem OMA.solution : type_of% @OMA.S_oeis_a171556.main := Deldor14.Catalan.result
