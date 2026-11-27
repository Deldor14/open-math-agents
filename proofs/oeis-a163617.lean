import OMAStatements.S_oeis_a163617
import Mathlib

namespace Deldor14.Gray
open OMA.S_oeis_a163617

private def gray (n : ℕ) := n ^^^ (n/2)
private theorem parity (n : ℕ) : ∃ k, n=2*k ∨ n=2*k+1 := ⟨n/2,by omega⟩
private theorem binary (m : ℕ) :
    gray (2*m)=2*gray m + m%2 ∧ gray (2*m+1)=2*gray m + (1-m%2) := by
  obtain ⟨k, rfl | rfl⟩ := parity m
  · have e := Nat.xor_bit false (2*k) false k
    have o := Nat.xor_bit true (2*k) false k
    simp [Nat.bit_false_apply,Nat.bit_true_apply] at e o
    simp [gray,show (2*(2*k)+1)/2=2*k by omega,show 2*k%2=0 by omega,e,o]
  · have e := Nat.xor_bit false (2*k+1) true k
    have o := Nat.xor_bit true (2*k+1) true k
    simp [Nat.bit_false_apply,Nat.bit_true_apply] at e o
    simp [gray,show (2*(2*k+1)+1)/2=2*k+1 by omega,show (2*k+1)/2=k by omega,
      show (2*k+1)%2=1 by omega,e,o]
private theorem evenA (m : ℕ) : a (2*m)=2*a m := by
  cases m with
  | zero => norm_num [a]
  | succ k =>
    rw [show 2*(k+1)=(2*k+1)+1 by omega,a,if_pos (by omega),show (2*k+1+1)/2=k+1 by omega]
private theorem oddA (m : ℕ) : a (2*m+1)=2*a m+2+(-1)^m := by
  rw [a,if_neg (by omega),show (2*m+1)/2=m by omega]
private theorem sign (m : ℕ) : (-1:ℤ)^m=1-2*(m%2:ℕ) := by
  obtain ⟨k, rfl | rfl⟩ := parity m
  · simp [pow_mul,show 2*k%2=0 by omega]
  · simp [pow_succ,pow_mul,show (2*k+1)%2=1 by omega]

theorem result : type_of% @OMA.S_oeis_a163617.main := by
  intro n
  change 4*a n=4*(gray n:ℤ)+(6*(n:ℤ)+1-(-1)^n)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n=0
    · subst n; norm_num [a,gray]
    obtain ⟨k, rfl | rfl⟩ := parity n
    · have h := ih k (by omega)
      rw [evenA,(binary k).1,pow_mul]
      norm_num
      push_cast
      rw [sign] at h
      omega
    · have h := ih k (by omega)
      rw [oddA,(binary k).2,pow_succ,pow_mul]
      have hb : k%2 ≤ 1 := by omega
      push_cast [Nat.cast_sub hb]
      rw [sign] at h ⊢
      norm_num
      omega

end Deldor14.Gray
theorem OMA.solution : type_of% @OMA.S_oeis_a163617.main := Deldor14.Gray.result
