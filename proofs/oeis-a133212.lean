import OMAStatements.S_oeis_a133212
import Mathlib

open OMA.S_oeis_a133212 Finset
namespace Deldor14.PascalFourth

/-- Residue-class sums in a row of Pascal's triangle. -/
private def part (n d : ℕ) : ℤ := ∑ j ∈ range (n+1), (n.choose (4*j+d):ℤ)

private theorem extendPart (n d : ℕ) :
    part n d=∑ j ∈ range (n+2), (n.choose (4*j+d):ℤ) := by
  rw [part,sum_range_succ (fun j => (n.choose (4*j+d):ℤ)) (n+1),Nat.choose_eq_zero_of_lt (by omega : n<4*(n+1)+d)]
  simp

private theorem above (n d : ℕ) : part (n+1) (d+1)=part n d + part n (d+1) := by
  rw [extendPart n d,extendPart n (d+1),part,← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rw [show 4*j+(d+1)=(4*j+d)+1 by omega,Nat.choose_succ_succ]
  push_cast
  ring

private theorem rollover (n : ℕ) : part (n+1) 0=part n 3+part n 0 := by
  unfold part
  simp only [Nat.add_zero]
  rw [sum_range_succ' (fun j => ((n+1).choose (4*j):ℤ)) (n+1)]
  rw [sum_range_succ' (fun j => (n.choose (4*j):ℤ)) n]
  have last : (∑ j ∈ range (n+1), (n.choose (4*(j+1)):ℤ)) =
      ∑ j ∈ range n,(n.choose (4*(j+1)):ℤ) := by
    rw [sum_range_succ,Nat.choose_eq_zero_of_lt (by omega : n<4*(n+1))]; simp
  have terms : (∑ j ∈ range (n+1), ((n+1).choose (4*(j+1)):ℤ)) =
      (∑ j ∈ range (n+1), (n.choose (4*j+3):ℤ)) +
      ∑ j ∈ range (n+1), (n.choose (4*(j+1)):ℤ) := by
    rw [← sum_add_distrib]; apply sum_congr rfl; intro j _
    rw [show 4*(j+1)=4*j+3+1 by omega,Nat.choose_succ_succ]; push_cast; ring
  rw [terms,last]
  simp; ring

private theorem binom (n : ℕ) : (b n:ℤ)=part n 0 := by
  simp only [b,part,Nat.add_zero,Nat.cast_sum]
  apply sum_subset (range_mono (by omega))
  intro j _ hj
  rw [Nat.choose_eq_zero_of_lt (by simp only [mem_range,not_lt] at hj; omega)]
  rfl

private theorem relation (n : ℕ) : part (n+4) 0=
    4*part (n+3) 0-6*part (n+2) 0+4*part (n+1) 0 := by
  simp only [rollover,above]
  ring

private theorem result (n : ℕ) : a (n+1)=2*(b (n+4):ℤ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n<3
    · interval_cases n <;> decide
    · obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
      change 4*a (k+3)-6*a (k+2)+4*a (k+1)=2*(b (k+7):ℤ)
      rw [ih (k+2) (by omega),ih (k+1) (by omega),ih k (by omega)]
      simp only [binom]
      linarith [relation (k+3)]

end Deldor14.PascalFourth
theorem OMA.solution : type_of% @OMA.S_oeis_a133212.main := by
  rintro (_|n) hn
  · omega
  · exact Deldor14.PascalFourth.result n
