import OMAStatements.S_oeis_a055278
import Mathlib

open PowerSeries OMA.S_oeis_a055278
namespace Deldor14.TreeGF

theorem translate (k b : ℕ) : A055278 (12*k+b) =
    432*(k:ℤ)^4 + (144*(b:ℤ)-240)*k^3 + (18*(b:ℤ)^2-60*b+54)*k^2 +
    ((b:ℤ)^3-5*b^2+9*b-5)*k + A055278 b := by
  unfold A055278
  push_cast
  have eqn (t x : ℤ) :
      3*(12*t+x)^4-20*(12*t+x)^3+54*(12*t+x)^2-60*(12*t+x)+32 =
      (432*t^4+(144*x-240)*t^3+(18*x^2-60*x+54)*t^2+(x^3-5*x^2+9*x-5)*t)*144 +
      (3*x^4-20*x^3+54*x^2-60*x+32) := by ring
  rw [eqn,Int.add_comm,Int.add_mul_ediv_right _ _ (by decide)]
  ring

theorem rec (j : ℕ) : A055278 (j+12)-3*A055278 (j+11)+2*A055278 (j+10)+
    A055278 (j+9)-A055278 (j+7)-2*A055278 (j+6)+3*A055278 (j+5)-A055278 (j+4)=0 := by
  obtain ⟨k,r,hr,rfl⟩ : ∃ k r, r<12 ∧ j=12*k+r :=
    ⟨j/12,j%12,Nat.mod_lt _ (by decide),by omega⟩
  simp only [Nat.add_assoc,translate]
  interval_cases r <;> norm_num [A055278] <;> ring

end Deldor14.TreeGF

theorem OMA.solution : type_of% @OMA.S_oeis_a055278.main := by
  let s : PowerSeries ℚ := mk fun n => (A055278 (n+4):ℚ)
  change s * _ = _
  have expansion : s*((1-X^2)*(1-X^3)*(1-X)^3) =
    s-(C (3:ℚ)*s)*X^1+(C (2:ℚ)*s)*X^2+s*X^3-s*X^5-(C (2:ℚ)*s)*X^6+
    (C (3:ℚ)*s)*X^7-s*X^8 := by simp only [map_ofNat]; ring
  rw [expansion]
  apply PowerSeries.ext
  intro n
  simp only [map_add,map_sub,coeff_mul_X_pow',coeff_C_mul,s,coeff_mk,coeff_X_pow,coeff_one]
  by_cases small : n<8
  · interval_cases n <;> norm_num [A055278]
  · obtain ⟨j,rfl⟩ : ∃ j,n=j+8 := ⟨n-8,by omega⟩
    simp only [if_pos (show 1≤j+8 by omega),if_pos (show 2≤j+8 by omega),
      if_pos (show 3≤j+8 by omega),if_pos (show 5≤j+8 by omega),
      if_pos (show 6≤j+8 by omega),if_pos (show 7≤j+8 by omega),if_pos (show 8≤j+8 by omega),
      if_neg (show j+8≠3 by omega),if_neg (show j+8≠2 by omega),if_neg (show j+8≠0 by omega),
      if_neg (show 3≠j+8 by omega),if_neg (show 2≠j+8 by omega),zero_add,add_zero]
    have h := Deldor14.TreeGF.rec j
    simp only [
      show j+8-1+4=j+11 by omega,show j+8-2+4=j+10 by omega,show j+8-3+4=j+9 by omega,
      show j+8-5+4=j+7 by omega,show j+8-6+4=j+6 by omega,show j+8-7+4=j+5 by omega,
      Nat.add_sub_cancel]
    exact_mod_cast h
