import OMAStatements.S_oeis_a203298
import Mathlib

namespace Deldor14.SymmetricPairs
open OMA.S_oeis_a203298 Finset
private def s (n : ℕ) := ∑ i ∈ Ico 1 (n+1),t i
private theorem ds (n : ℕ) : s (n+1)=s n+t (n+1) := by
  unfold s
  rw [sum_Ico_succ_top (by omega : 1≤n+1)]
private theorem da (n : ℕ) : a (n+1)=a n+s n*t (n+1) := by
  unfold a s
  rw [sum_Icc_succ_top (by omega : 1≤n+1),sum_mul]
private def E (n : ℤ) := 6*n^4+40*n^3+48*n^2-112*n
private def O (n : ℤ) := 6*n^4+40*n^3+36*n^2-136*n+54
private theorem first (k : ℕ) : s (2*k)=k*(k+2) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 2*(k+1)=2*k+1+1 by omega,ds,ds,ih]
    simp only [t,show (2*k+1+2)/2=k+1 by omega,show (2*k+1+1+2)/2=k+2 by omega]
    ring
private theorem evenA (k : ℕ) : 192*(a (2*k):ℤ)=E (2*k) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 2*(k+1)=2*k+1+1 by omega,da,da,ds,first]
    simp only [t,show (2*k+1+2)/2=k+1 by omega,show (2*k+1+1+2)/2=k+2 by omega]
    push_cast
    unfold E at *
    linear_combination ih
private theorem oddA (k : ℕ) : 192*(a (2*k+1):ℤ)=O (2*k+1) := by
  rw [da,first]
  simp only [t,show (2*k+1+2)/2=k+1 by omega]
  push_cast
  have h := evenA k
  unfold O E at *
  linear_combination h
private theorem val (n : ℕ) : 192*(a n:ℤ)=if n%2=0 then E n else O n := by
  rcases Nat.even_or_odd n with h|h
  · obtain ⟨k,e⟩ := h
    rw [if_pos (by omega),show n=2*k by omega]
    simpa using evenA k
  · obtain ⟨k,e⟩ := h
    rw [if_neg (by omega),show n=2*k+1 by omega]
    simpa using oddA k
private theorem recA (n : ℕ) (hn : 9<n) :
    (a n:ℤ)=2*a (n-1)+2*a (n-2)-6*a (n-3)+6*a (n-5)-2*a (n-6)-2*a (n-7)+a (n-8) := by
  obtain ⟨k,rfl⟩ : ∃ k,n=k+8 := ⟨n-8,by omega⟩
  simp only [show k+8-1=k+7 by omega,show k+8-2=k+6 by omega,show k+8-3=k+5 by omega,
    show k+8-5=k+3 by omega,show k+8-6=k+2 by omega,show k+8-7=k+1 by omega,Nat.add_sub_cancel]
  apply mul_left_cancel₀ (show (192:ℤ)≠0 by decide)
  have v (j : ℕ) : 192*(a (k+j):ℤ)=if (k%2+j%2)%2=0 then E ((k:ℤ)+j) else O ((k:ℤ)+j) := by
    simpa only [← Nat.add_mod,Nat.cast_add] using val (k+j)
  have v₈ := v 8
  have v₇ := v 7
  have v₆ := v 6
  have v₅ := v 5
  have v₃ := v 3
  have v₂ := v 2
  have v₁ := v 1
  have v₀ := v 0
  have rem := Nat.mod_lt k (by decide : 0<2)
  interval_cases k%2 <;> norm_num [E,O] at v₈ v₇ v₆ v₅ v₃ v₂ v₁ v₀ <;>
    linear_combination v₈-2*v₇-2*v₆+6*v₅-6*v₃+2*v₂+2*v₁-v₀

theorem result : type_of% @OMA.S_oeis_a203298.main := by
  refine ⟨?_,?_,recA⟩
  · intro n _ hn
    have h := val n
    rw [if_pos (Nat.even_iff.mp hn)] at h
    unfold E at h
    apply (eq_div_iff (by norm_num)).2
    rw [mul_comm]
    exact_mod_cast h
  · intro n _ hn
    have h := val n
    rw [if_neg (by obtain ⟨k,e⟩ := hn;omega)] at h
    unfold O at h
    apply (eq_div_iff (by norm_num)).2
    rw [mul_comm]
    exact_mod_cast h
end Deldor14.SymmetricPairs
theorem OMA.solution : type_of% @OMA.S_oeis_a203298.main := Deldor14.SymmetricPairs.result
