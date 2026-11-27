import OMAStatements.S_oeis_a182025
import Mathlib

namespace Deldor14.BinomialTail
open OMA.S_oeis_a182025 Finset

private def row (k j : ℕ) : ℤ := (2*(k+4)).choose j
private theorem adj (k j : ℕ) (hj : j≤k) :
    row k (j+1)*((j:ℤ)+1)=row k j*(2*((k:ℤ)+4)-j) := by
  have h := congrArg (fun z : ℕ => (z:ℤ)) (Nat.choose_succ_right_eq (2*(k+4)) j)
  push_cast [Nat.cast_sub (by omega : j≤2*(k+4))] at h
  exact h
private theorem telescope (k t : ℕ) (ht : t≤k) :
    2*(∑ i ∈ Icc 1 t, row k (k-i)*(4+(i:ℤ))) =
      (k:ℤ)*row k k-((k:ℤ)-t)*row k (k-t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have prev := ih (by omega)
    let j := k-(t+1)
    have je : k-t=j+1 := by dsimp [j];omega
    have jc : (j:ℤ)=(k:ℤ)-(t+1) := by dsimp [j];rw [Nat.cast_sub ht];push_cast;rfl
    have h := adj k j (by dsimp [j];omega)
    rw [Finset.sum_Icc_succ_top (by omega : 1≤t+1)]
    rw [je] at prev
    change 2*((∑ i ∈ Icc 1 t,row k (k-i)*(4+(i:ℤ)))+row k j*(4+((t+1:ℕ):ℤ))) = _-_*row k j
    push_cast
    rw [jc] at h
    linear_combination prev - h
private theorem closed (k : ℕ) : 2*a (k+4)=((k:ℤ)+62)*row k k := by
  have h := telescope k k (le_refl _)
  simp only [sub_self,zero_mul,sub_zero] at h
  unfold a
  rw [if_neg (by omega),Nat.add_sub_cancel]
  change 2*(31*row k k+∑ i ∈ Icc 1 k,row k (k-i)*(4+(i:ℤ)))=_
  linear_combination h
private theorem factorial (k : ℕ) :
    row k k*(k.factorial:ℤ)*((k+8).factorial:ℤ)=((2*k+8).factorial:ℤ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (n:=2*(k+4)) (k:=k) (by omega)
  rw [show 2*(k+4)-k=k+8 by omega,show 2*(k+4)=2*k+8 by omega] at h
  unfold row
  rw [show 2*(k+4)=2*k+8 by omega]
  exact_mod_cast h
private theorem step (k : ℕ) :
    ((k:ℤ)+1)*(k+9)*row (k+1) (k+1)=(2*(k:ℤ)+10)*(2*k+9)*row k k := by
  have h := factorial (k+1)
  rw [show k+1+8=k+8+1 by omega,show 2*(k+1)+8=2*k+8+1+1 by omega,
    Nat.factorial_succ (2*k+8+1),Nat.factorial_succ (2*k+8),Nat.factorial_succ (k+8),Nat.factorial_succ k] at h
  push_cast at h
  apply mul_right_cancel₀ (show (k.factorial:ℤ)*(k+8).factorial≠0 by positivity)
  linear_combination h - (2*(k:ℤ)+10)*(2*k+9)*factorial k

theorem result : type_of% @OMA.S_oeis_a182025.main := by
  intro n hn
  by_cases sm : n<6
  · interval_cases n <;> decide
  obtain ⟨k,rfl⟩ : ∃ k,n=k+6 := ⟨n-6,by omega⟩
  rw [show k+6-1=k+5 by omega,show k+6-2=k+4 by omega]
  push_cast
  have c₂ := closed (k+2)
  have c₁ := closed (k+1)
  have s := step (k+1)
  push_cast at c₂ c₁ s
  rw [show k+2+4=k+6 by omega] at c₂
  rw [show k+1+4=k+5 by omega] at c₁
  apply mul_left_cancel₀ (show (2:ℤ)≠0 by decide)
  linear_combination 558*((k:ℤ)+2)*(k+10)*c₂ + 7*(-631*((k:ℤ)+6)^2+777*(k+6)+4600)*c₁ +
    4370*((k:ℤ)+5)*(2*k+9)*closed k + 558*((k:ℤ)+64)*s - 2185*((k:ℤ)+62)*step k
end Deldor14.BinomialTail
theorem OMA.solution : type_of% @OMA.S_oeis_a182025.main := Deldor14.BinomialTail.result
