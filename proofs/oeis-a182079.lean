import OMAStatements.S_oeis_a182079
import Mathlib

namespace Deldor14.FloorSeries
open OMA.S_oeis_a182079 PowerSeries
private theorem term (n : ℕ) : a n=((n:ℤ)*(((n:ℤ)-1)/2))/3 := by
  have inner := Rat.floor_intCast_div_natCast ((n:ℤ)-1) 2
  push_cast at inner
  unfold a
  rw [inner]
  simpa only [Int.cast_mul,Int.cast_natCast,Nat.cast_ofNat] using
    Rat.floor_intCast_div_natCast ((n:ℤ)*(((n:ℤ)-1)/2)) 3
private theorem shift (n : ℕ) : a (n+6)=a n+2*(((n:ℤ)-1)/2)+n+6 := by
  rw [term,term]
  push_cast
  rw [show ((n:ℤ)+6-1)/2=((n:ℤ)-1)/2+3 by omega]
  have h : ((n:ℤ)+6)*(((n:ℤ)-1)/2+3) =
      (n:ℤ)*(((n:ℤ)-1)/2)+(2*(((n:ℤ)-1)/2)+n+6)*3 := by ring
  rw [h,Int.add_mul_ediv_right _ _ (by decide : (3:ℤ)≠0)]
  ring
private theorem recA (n : ℕ) :
    a (n+9)-a (n+8)-a (n+7)+a (n+6)-a (n+3)+a (n+2)+a (n+1)-a n=0 := by
  have h₀ := shift n
  have h₁ := shift (n+1)
  have h₂ := shift (n+2)
  have h₃ := shift (n+3)
  push_cast at h₁ h₂ h₃
  rw [show n+1+6=n+7 by omega] at h₁
  rw [show n+2+6=n+8 by omega,show ((n:ℤ)+2-1)/2=((n:ℤ)-1)/2+1 by omega] at h₂
  rw [show n+3+6=n+9 by omega,show ((n:ℤ)+3-1)/2=((n:ℤ)+1-1)/2+1 by omega] at h₃
  omega
theorem result : type_of% @OMA.S_oeis_a182079.main := by
  let f := mk a
  have left : f*((1-X)^3*(1+X)^2*(X^2-X+1)*(X^2+X+1) : PowerSeries ℤ)=
      f-f*X-f*X^2+f*X^3-f*X^6+f*X^7+f*X^8-f*X^9 := by ring
  have right : (X^3*(X^4+X^3+X^2+1):PowerSeries ℤ)=X^7+X^6+X^5+X^3 := by ring
  change f*_=_
  rw [left,right]
  apply PowerSeries.ext
  intro n
  have x : coeff n (f*X)=if 1≤n then coeff (n-1) f else 0 := by
    simpa only [pow_one] using coeff_mul_X_pow' f 1 n
  simp only [map_add,map_sub,x,coeff_mul_X_pow',coeff_X_pow,f,coeff_mk]
  by_cases sm : n<9
  · interval_cases n <;> norm_num [term]
  · obtain ⟨k,rfl⟩ : ∃ k,n=k+9 := ⟨n-9,by omega⟩
    simp only [if_pos (by omega : 1≤k+9),if_pos (by omega : 2≤k+9),if_pos (by omega : 3≤k+9),
      if_pos (by omega : 6≤k+9),if_pos (by omega : 7≤k+9),if_pos (by omega : 8≤k+9),if_pos (by omega : 9≤k+9),
      if_neg (by omega : k+9≠7),if_neg (by omega : k+9≠6),if_neg (by omega : k+9≠5),if_neg (by omega : k+9≠3)]
    simpa using recA k
end Deldor14.FloorSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a182079.main := Deldor14.FloorSeries.result
