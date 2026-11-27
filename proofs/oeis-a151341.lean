import OMAStatements.S_oeis_a151341
import Mathlib

namespace Deldor14.MotzkinDyck
open OMA.S_oeis_a151341
private theorem cat (n : ℕ) : ((n:ℚ)+2)*catalan (n+1)=2*(2*n+1)*(catalan n:ℚ) := by
  have h := congrArg (fun z : ℕ => (z:ℚ)) (Nat.succ_mul_centralBinom_succ n)
  rw [← succ_mul_catalan_eq_centralBinom,← succ_mul_catalan_eq_centralBinom] at h
  push_cast at h
  apply mul_left_cancel₀ (show (n:ℚ)+1≠0 by positivity)
  linear_combination h
theorem result : type_of% @OMA.S_oeis_a151341.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+2 := ⟨n-2,by omega⟩
  simp only [a,show k+2-1=k+1 by omega,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_ofNat]
  have m : motzkin (k+2)*((k:ℚ)+4)=(2*k+5)*motzkin (k+1)+3*(k+1)*motzkin k := by
    rw [motzkin,div_mul_cancel₀ _ (by positivity)]
  have c := cat (k+1)
  push_cast at c
  linear_combination ((k:ℚ)+2)*(k+3)*(catalan (k+2):ℚ)*m+
    ((k:ℚ)+2)*((2*k+5)*motzkin (k+1)+3*(k+1)*motzkin k)*c+
    6*((k:ℚ)+1)*(2*k+3)*motzkin k*cat k
end Deldor14.MotzkinDyck
theorem OMA.solution : type_of% @OMA.S_oeis_a151341.main := Deldor14.MotzkinDyck.result
