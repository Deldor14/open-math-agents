import OMAStatements.S_oeis_a037958
import Mathlib

open OMA.S_oeis_a037958
namespace Deldor14.Binomial037958

private theorem evenCase (k : ℕ) :
    -((2*k+10:ℤ)+9)*((2*k+10:ℤ)-8)*((2*k+10).choose (k+1):ℤ)+2*(2*k+10:ℤ)*((2*k+9).choose (k):ℤ)+4*(2*k+10:ℤ)*((2*k+10:ℤ)-1)*((2*k+8).choose k:ℤ)=0 := by
  have h := Nat.add_one_mul_choose_eq (2*k+9) k
  have g := Nat.choose_mul_succ_eq (2*k+8) k
  rw [show 2*k+8+1-k=k+9 by omega] at g
  zify at h g
  linear_combination 2*((2*k+10:ℤ)+9)*h+4*(2*k+10:ℤ)*g

private theorem oddCase (k : ℕ) :
    -((2*k+11:ℤ)+9)*((2*k+11:ℤ)-8)*((2*k+11).choose (k+1):ℤ)+2*(2*k+11:ℤ)*((2*k+10).choose (k+1):ℤ)+4*(2*k+11:ℤ)*((2*k+11:ℤ)-1)*((2*k+9).choose k:ℤ)=0 := by
  have h := Nat.choose_mul_succ_eq (2*k+10) (k+1)
  have g := Nat.add_one_mul_choose_eq (2*k+9) k
  rw [show 2*k+10+1-(k+1)=k+10 by omega] at h
  zify at h g
  linear_combination 2*((2*k+11:ℤ)-8)*h+4*(2*k+11:ℤ)*g

theorem result : type_of% @OMA.S_oeis_a037958.main := by
  intro n hn
  by_cases small : n<10
  · interval_cases n <;> norm_num [a,Nat.choose]
  let k := (n-10)/2
  have parity : n=2*k+10 ∨ n=2*k+11 := by dsimp [k];omega
  rcases parity with e | e
  · rw [e]
    simp only [show 2*k+10-1=2*k+9 by omega,show 2*k+10-2=2*k+8 by omega,a,if_neg (by omega : ¬(2*k+10<8)),if_neg (by omega : ¬(2*k+9<8)),if_neg (by omega : ¬(2*k+8<8))]
    rw [show (2*k+10-8)/2=k+1 by omega]
    rw [show (2*k+9-8)/2=k by omega]
    rw [show (2*k+8-8)/2=k by omega]
    have h := evenCase k
    push_cast
    exact h
  · rw [e]
    simp only [show 2*k+11-1=2*k+10 by omega,show 2*k+11-2=2*k+9 by omega,a,if_neg (by omega : ¬(2*k+11<8)),if_neg (by omega : ¬(2*k+10<8)),if_neg (by omega : ¬(2*k+9<8))]
    rw [show (2*k+11-8)/2=k+1 by omega]
    rw [show (2*k+10-8)/2=k+1 by omega]
    rw [show (2*k+9-8)/2=k by omega]
    have h := oddCase k
    push_cast
    exact h
end Deldor14.Binomial037958

theorem OMA.solution : type_of% @OMA.S_oeis_a037958.main := Deldor14.Binomial037958.result
