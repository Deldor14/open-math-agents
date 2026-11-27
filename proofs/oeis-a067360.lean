import OMAStatements.S_oeis_a067360
import Mathlib

namespace Deldor14.SinePowers
open OMA.S_oeis_a067360 Complex
private noncomputable def θ : ℝ := 2*Real.arctan (1/4)
private theorem trig : Real.cos θ=15/17 ∧ Real.sin θ=8/17 := by
  have c := Real.cos_sq_arctan (1/4)
  norm_num at c
  have t := Real.tan_mul_cos (Real.cos_arctan_pos (1/4)).ne'
  rw [Real.tan_arctan] at t
  unfold θ
  rw [Real.cos_two_mul, Real.sin_two_mul]
  constructor
  · linarith
  · rw [← t]
    nlinarith
private theorem form (s : ℂ) (hs : s^2= -1) (n : ℕ) :
    (15+8*s)^n=(17:ℂ)^n*((Real.cos ((n:ℝ)*θ):ℂ)+(Real.sin ((n:ℝ)*θ):ℂ)*s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,pow_succ,ih,Nat.cast_add_one,add_mul,one_mul,Real.cos_add,Real.sin_add,trig.1,trig.2]
    push_cast
    linear_combination 8*(17:ℂ)^n*Complex.sin ((n:ℂ)*(θ:ℂ))*hs
private theorem closed (n : ℕ) : (a n:ℂ)=I*((15-8*I)^n-(15+8*I)^n)/2 := by
  have hm := form (-I) (by simp [I_sq]) n
  rw [show (15:ℂ)+8*(-I)=15-8*I by ring] at hm
  rw [hm,form I I_sq]
  unfold a
  rw [show 2*(n:ℝ)*Real.arctan (1/4)=(n:ℝ)*θ by unfold θ;ring]
  push_cast
  linear_combination (17:ℂ)^n*Complex.sin ((n:ℂ)*(θ:ℂ))*I_sq
theorem result : type_of% @OMA.S_oeis_a067360.main := by
  refine ⟨?_,fun n _ => closed n⟩
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+2 := ⟨n-2,by omega⟩
  rw [show k+2-1=k+1 by omega,Nat.add_sub_cancel]
  apply Complex.ofReal_injective
  push_cast
  rw [closed,closed,closed]
  simp only [pow_add,pow_one]
  have hp : (15+8*I)^2=30*(15+8*I)-289 := by linear_combination 64*I_sq
  have hm : (15-8*I)^2=30*(15-8*I)-289 := by linear_combination 64*I_sq
  rw [hp,hm];ring
end Deldor14.SinePowers
theorem OMA.solution : type_of% @OMA.S_oeis_a067360.main := Deldor14.SinePowers.result
