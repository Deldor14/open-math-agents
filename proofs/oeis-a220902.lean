import OMAStatements.S_oeis_a220902
import Mathlib

namespace Deldor14.AlternatingCatalan
open OMA.S_oeis_a220902
private theorem recC (n : ℕ) : ((n:ℤ)+2)*catalan (n+1)=2*(2*n+1)*(catalan n:ℤ) := by
  have h := congrArg (fun z : ℕ => (z:ℤ)) (Nat.succ_mul_centralBinom_succ n)
  rw [← succ_mul_catalan_eq_centralBinom,← succ_mul_catalan_eq_centralBinom] at h
  push_cast at h
  apply mul_left_cancel₀ (show (n:ℤ)+1≠0 by positivity)
  linear_combination h

theorem result : type_of% @OMA.S_oeis_a220902.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+5 := ⟨n-5,by omega⟩
  unfold a
  simp only [show k+5-1=k+4 by omega,
    show k+5-2=k+3 by omega,
    show k+5-3=k+2 by omega,
    show k+4-1=k+3 by omega,
    show k+4-2=k+2 by omega,
    show k+4-3=k+1 by omega,
    show k+3-1=k+2 by omega,
    show k+3-2=k+1 by omega,
    show k+3-3=k by omega,
    show k+2-1=k+1 by omega,
    show k+2-2=k by omega,Nat.cast_add,Nat.cast_ofNat]
  have h₄ := recC (k+4)
  have h₃ := recC (k+3)
  have h₂ := recC (k+2)
  have h₁ := recC (k+1)
  push_cast at h₄ h₃ h₂ h₁
  linear_combination h₄-2*h₃+3*h₂-2*h₁+recC k
end Deldor14.AlternatingCatalan
theorem OMA.solution : type_of% @OMA.S_oeis_a220902.main := Deldor14.AlternatingCatalan.result
