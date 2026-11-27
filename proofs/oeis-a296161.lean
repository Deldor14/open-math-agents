import OMAStatements.S_oeis_a296161
import Mathlib

open OMA.S_oeis_a296161
namespace Deldor14.Partitions

private theorem partialSum (n j : ℕ) (hj : j ≤ n) :
    ((∑ i ∈ Finset.Icc 1 j, (n-i)*(i%2) : ℕ) : ℤ) =
    ((j+1)/2 : ℕ) * ((n:ℤ)-((j+1)/2 : ℕ)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j+1)]
    rw [Nat.cast_add, ih (by omega),Nat.cast_mul,Nat.cast_sub (by omega : j+1 ≤ n)]
    by_cases even : (j+1)%2=0
    · rw [even,show (j+1+1)/2=(j+1)/2 by omega]
      push_cast
      ring
    · rw [show (j+1)%2=1 by omega,show (j+1+1)/2=(j+1)/2+1 by omega]
      have e : j+1=2*((j+1)/2)+1 := by omega
      have eq : (j:ℤ)+1=2*(((j+1)/2:ℕ):ℤ)+1 := by exact_mod_cast e
      push_cast
      linarith

private def count (n : ℕ) : ℕ := (n+2)/4

private theorem formula (n : ℕ) : (a n:ℤ) = count n * ((n:ℤ)-count n) := by
  unfold a count
  rw [partialSum n (n/2) (by omega),show (n/2+1)/2=(n+2)/4 by omega]

private theorem delta (n : ℕ) : (a (n+8):ℤ)-2*a (n+4)+a n=6 := by
  have four : count (n+4)=count n+1 := by unfold count;omega
  have eight : count (n+8)=count n+2 := by unfold count;omega
  rw [formula,formula,formula,eight,four]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 9<n) :
    (a n:ℤ)=a (n-1)+2*a (n-4)-2*a (n-5)-a (n-8)+a (n-9) := by
  have h := delta (n-8)
  have h' := delta (n-9)
  rw [show n-8+8=n by omega,show n-8+4=n-4 by omega] at h
  rw [show n-9+8=n-1 by omega,show n-9+4=n-5 by omega] at h'
  linarith
end Deldor14.Partitions

theorem OMA.solution : type_of% @OMA.S_oeis_a296161.main := Deldor14.Partitions.recurrence
