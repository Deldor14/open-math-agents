import OMAStatements.S_oeis_a066534
import Mathlib

open OMA.S_oeis_a066534
namespace Deldor14.BooleanWalk

private theorem step (n : ℕ) : a (n+1)=(n+1)*(a n+2^n) := by
  simp only [a,Finset.sum_range_succ,Nat.factorial_succ n,Nat.mul_add,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial (Finset.mem_range.mp hi).le)]
    ring
  · simp [Nat.factorial_ne_zero]

theorem result (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℤ)+(-(n:ℤ)-4)*a (n-1)+4*(n:ℤ)*a (n-2)+4*(-(n:ℤ)+2)*a (n-3)=0 := by
  obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3, by omega⟩
  simp only [show k+3-1=k+2 by omega,show k+3-2=k+1 by omega,Nat.add_sub_cancel]
  rw [step (k+2),step (k+1),step k]
  push_cast
  simp only [pow_succ]
  ring
end Deldor14.BooleanWalk

theorem OMA.solution : type_of% @OMA.S_oeis_a066534.main := Deldor14.BooleanWalk.result
