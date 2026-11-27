import OMAStatements.S_oeis_a112700
import Mathlib

namespace Deldor14.CatalanSum
open OMA.S_oeis_a112700
private theorem recC (n : ℕ) : ((n:ℤ)+2)*catalan (n+1)=2*(2*n+1)*(catalan n:ℤ) := by
  have h := congrArg (fun z : ℕ => (z:ℤ)) (Nat.succ_mul_centralBinom_succ n)
  rw [← succ_mul_catalan_eq_centralBinom,← succ_mul_catalan_eq_centralBinom] at h
  push_cast at h
  apply mul_left_cancel₀ (show (n:ℤ)+1≠0 by positivity)
  linear_combination h
private theorem diff (n : ℕ) : (a (n+1):ℤ)=(a n:ℤ)+6^(n+1)*(catalan (n+1):ℤ) := by
  unfold a
  rw [Finset.sum_range_succ]
  push_cast
  rfl
theorem result : type_of% @OMA.S_oeis_a112700.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+2 := ⟨n-2,by omega⟩
  simp only [show k+2-1=k+1 by omega,show k+2-2=k by omega,Nat.cast_add,Nat.cast_ofNat]
  rw [diff (k+1),diff k]
  have h := recC (k+1)
  push_cast at h
  simp only [pow_succ]
  linear_combination 36*(6:ℤ)^k*h
end Deldor14.CatalanSum
theorem OMA.solution : type_of% @OMA.S_oeis_a112700.main := Deldor14.CatalanSum.result
