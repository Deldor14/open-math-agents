import OMAStatements.S_oeis_a002867
import Mathlib

open OMA.S_oeis_a002867
namespace Deldor14.Binomial002867

private theorem evenCase (k : ℕ) :
    ((2*k+2:ℤ)+1)*((2*k+2).choose (k+1):ℤ)-2*((2*k+1).choose (k):ℤ)-4*((2*k+2:ℤ)-1)*((2*k).choose k:ℤ)=0 := by
  have h := Nat.add_one_mul_choose_eq (2*k+1) k
  have g := Nat.choose_mul_succ_eq (2*k) k
  rw [show 2*k+1-k=k+1 by omega] at g
  zify at h g
  have double : ((2*k+2).choose (k+1):ℤ)=2*((2*k+1).choose (k):ℤ) := by
    apply mul_left_cancel₀ (by positivity : (k:ℤ)+1≠0)
    linear_combination -h
  rw [double]
  linear_combination -4*g

private theorem oddCase (k : ℕ) :
    ((2*k+3:ℤ)+1)*((2*k+3).choose (k+1):ℤ)-2*((2*k+2).choose (k+1):ℤ)-4*((2*k+3:ℤ)-1)*((2*k+1).choose k:ℤ)=0 := by
  have h := Nat.choose_mul_succ_eq (2*k+2) (k+1)
  have g := Nat.add_one_mul_choose_eq (2*k+1) k
  rw [show 2*k+2+1-(k+1)=k+2 by omega] at h
  zify at h g
  linear_combination -2*h-4*g

theorem result : type_of% @OMA.S_oeis_a002867.main := by
  intro n hn
  let k := (n-2)/2
  have parity : n=2*k+2 ∨ n=2*k+3 := by dsimp [k];omega
  rcases parity with e | e
  · rw [e]
    simp only [show 2*k+2-1=2*k+1 by omega,show 2*k+2-2=2*k by omega,a]
    rw [show (2*k+2)/2=k+1 by omega]
    rw [show (2*k+1)/2=k by omega]
    rw [show (2*k)/2=k by omega]
    have h := evenCase k
    rw [show 2*k+2+1=(2*k+1+1)+1 by omega,Nat.factorial_succ (2*k+1+1),Nat.factorial_succ (2*k+1)]
    push_cast
    linear_combination ((2*k+1:ℤ)+1)*((2*k+1).factorial:ℤ)*h
  · rw [e]
    simp only [show 2*k+3-1=2*k+2 by omega,show 2*k+3-2=2*k+1 by omega,a]
    rw [show (2*k+3)/2=k+1 by omega]
    rw [show (2*k+2)/2=k+1 by omega]
    rw [show (2*k+1)/2=k by omega]
    have h := oddCase k
    rw [show 2*k+3+1=(2*k+2+1)+1 by omega,Nat.factorial_succ (2*k+2+1),Nat.factorial_succ (2*k+1+1)]
    push_cast
    linear_combination ((2*k+2:ℤ)+1)*((2*k+1+1).factorial:ℤ)*h
end Deldor14.Binomial002867

theorem OMA.solution : type_of% @OMA.S_oeis_a002867.main := Deldor14.Binomial002867.result
