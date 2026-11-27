import OMAStatements.S_oeis_a079269
import Mathlib

namespace Deldor14.RationalIterate
open OMA.S_oeis_a079269
private def pair : ℕ → ℕ × ℕ
  | 0 => (1,1)
  | k+1 => let (p,q) := pair k; (p*(p+2*q),q*(p+q))
private theorem inc (k : ℕ) :
    (pair (k+1)).1=(pair k).1*((pair k).1+2*(pair k).2) ∧
    (pair (k+1)).2=(pair k).2*((pair k).1+(pair k).2) := by
  constructor <;> rfl
private theorem props (k : ℕ) : 0<(pair k).1 ∧ 0<(pair k).2 ∧ (pair k).1.Coprime (pair k).2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨hp,hq,h⟩ := ih
    rw [(inc k).1,(inc k).2]
    refine ⟨by positivity,by positivity,?_⟩
    rw [Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_right,Nat.coprime_mul_iff_right]
    refine ⟨⟨h,Nat.coprime_self_add_right.mpr h⟩,⟨(Nat.coprime_add_mul_right_left _ _ _).mpr h,?_⟩⟩
    rw [show (pair k).1+2*(pair k).2=(pair k).2+((pair k).1+(pair k).2) by omega,
      Nat.coprime_add_self_left,Nat.coprime_add_self_right]
    exact h.symm
private theorem val (k : ℕ) : iterate k=((pair k).1:ℚ)/(pair k).2 := by
  induction k with
  | zero => norm_num [iterate,pair]
  | succ k ih =>
    obtain ⟨hp,hq,_⟩ := props k
    have pp : 0<((pair k).1:ℚ) := by exact_mod_cast hp
    have pq : 0<((pair k).2:ℚ) := by exact_mod_cast hq
    rw [iterate,ih,(inc k).1,(inc k).2]
    push_cast
    field_simp
    <;> ring
private theorem numerator (k : ℕ) : a (k+1)=(pair k).1 := by
  obtain ⟨_,q,c⟩ := props k
  rw [a,Nat.add_sub_cancel,val]
  simpa using Rat.num_div_eq_of_coprime (a:=((pair k).1:ℤ)) (b:=((pair k).2:ℤ)) (by exact_mod_cast q) (by simpa)
theorem result : type_of% @OMA.S_oeis_a079269.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+2 := ⟨n-2,by omega⟩
  rw [show k+2-1=k+1 by omega,numerator (k+2),numerator (k+1),numerator k,(inc (k+1)).1,(inc k).1,(inc k).2]
  push_cast
  have hp : 0<((pair k).1:ℚ) := by exact_mod_cast (props k).1
  field_simp
  <;> ring
end Deldor14.RationalIterate
theorem OMA.solution : type_of% @OMA.S_oeis_a079269.main := Deldor14.RationalIterate.result
