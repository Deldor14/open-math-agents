import OMAStatements.S_oeis_a127628
import Mathlib

namespace Deldor14.Ballot
open OMA.S_oeis_a127628 Finset

private def row (n k : ℕ) : ℚ := (2*n).choose (n+k)
private def ballot (n k : ℕ) := row n k-row n (k+1)
private def value (n k : ℕ) : ℚ := 5^k*ballot n k
private def flux (n k : ℕ) : ℚ := 5^(k+1)*(ballot n (k+1)-5*ballot n k)

private theorem outside (n k : ℕ) (hk : n<k) : ballot n k=0 := by
  simp [ballot,row,Nat.choose_eq_zero_of_lt (show 2*n<n+k by omega),
    Nat.choose_eq_zero_of_lt (show 2*n<n+(k+1) by omega)]

private theorem factor (n k : ℕ) (hk : k≤n) :
    ballot n k*((n:ℚ)+k+1) = row n k*(2*k+1) := by
  have le : n+k ≤ 2*n := by omega
  have h := congrArg (fun z : ℕ => (z:ℚ)) (Nat.choose_succ_right_eq (2*n) (n+k))
  push_cast [Nat.cast_sub le] at h
  change ((↑((2*n).choose (n+k)):ℚ) - ↑((2*n).choose ((n+k)+1)))*_=_
  unfold row
  linarith only [h]

private theorem asSum (n : ℕ) : a n=∑ k ∈ range (n+1), value n k := by
  unfold a
  apply sum_congr rfl
  intro k hk
  have le : k≤n := by simpa using hk
  have c : (2*n).choose (n-k)=(2*n).choose (n+k) := Nat.choose_symm_of_eq_add (by omega)
  rw [c]
  apply (div_eq_iff (by positivity)).2
  change row n k*(2*k+1)*5^k = (5^k*ballot n k)*_
  linear_combination -(5:ℚ)^k * factor n k le

private theorem middle (n : ℕ) : row (n+1) 0=2*row n 0+2*row n 1 := by
  unfold row
  simp only [Nat.add_zero,show 2*(n+1)=2*n+1+1 by omega]
  rw [Nat.choose_succ_succ,← Nat.choose_symm_half, Nat.choose_succ_succ]
  push_cast
  ring

private theorem interior (n k : ℕ) : row (n+1) (k+1)=row n k+2*row n (k+1)+row n (k+2) := by
  unfold row
  rw [show 2*(n+1)=2*n+1+1 by omega,show n+1+(k+1)=n+k+1+1 by omega,
    Nat.choose_succ_succ,Nat.choose_succ_succ,Nat.choose_succ_succ]
  push_cast
  change (row n k+row n (k+1))+(row n (k+1)+row n (k+2))=row n k+2*row n (k+1)+row n (k+2)
  ring

private theorem edge (n : ℕ) : ballot (n+1) 0=ballot n 0+ballot n 1 := by
  unfold ballot
  rw [middle,interior n 0]
  ring
private theorem inner (n k : ℕ) : ballot (n+1) (k+1)=ballot n k+2*ballot n (k+1)+ballot n (k+2) := by
  unfold ballot
  rw [interior,interior]
  ring

private theorem telescope (n t : ℕ) :
    5*(∑ k ∈ range (t+1),value (n+1) k)-36*(∑ k ∈ range (t+1),value n k) =
      flux n t-6*ballot n 0 := by
  induction t with
  | zero => simp [value,flux,edge]; ring
  | succ t ih =>
    rw [sum_range_succ (n:=t+1),sum_range_succ (n:=t+1)]
    simp only [value,flux,inner,pow_succ] at *
    linear_combination ih

private theorem weighted (n : ℕ) : 5*a (n+1)-36*a n = -6*ballot n 0 := by
  have h := telescope n (n+1)
  have z₁ := outside n (n+1) (by omega)
  have z₂ := outside n (n+2) (by omega)
  rw [show (∑ k ∈ range (n+1+1),value n k)=(∑ k ∈ range (n+1),value n k)+value n (n+1) by rw [sum_range_succ],
    ← asSum,← asSum] at h
  simpa [flux,value,z₁,z₂] using h

private theorem center (n : ℕ) : ((n:ℚ)+2)*ballot (n+1) 0=2*(2*n+1)*ballot n 0 := by
  have f := factor (n+1) 0 (by omega)
  have g := factor n 0 (by omega)
  simp only [Nat.cast_zero,Nat.cast_add,Nat.cast_one,add_zero,mul_zero,zero_add,mul_one] at f g
  have h := congrArg (fun z : ℕ => (z:ℚ)) (Nat.succ_mul_centralBinom_succ n)
  change ((↑((n+1)*((n+1).centralBinom)):ℚ)) = _ at h
  push_cast at h
  change ((n:ℚ)+1)*row (n+1) 0 = 2*(2*(n:ℚ)+1)*row n 0 at h
  apply (mul_left_cancel₀ (show (n:ℚ)+1≠0 by positivity))
  linear_combination ((n:ℚ)+1)*f + h - (2*(2*(n:ℚ)+1))*g

theorem result : type_of% @OMA.S_oeis_a127628.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+2 := ⟨n-2,by omega⟩
  simp only [show k+2-1=k+1 by omega,show k+2-2=k by omega,Nat.cast_add,Nat.cast_ofNat]
  linear_combination ((k:ℚ)+2)*weighted (k+1) - 2*(2*(k:ℚ)+1)*weighted k - 6*center k

end Deldor14.Ballot
theorem OMA.solution : type_of% @OMA.S_oeis_a127628.main := Deldor14.Ballot.result
