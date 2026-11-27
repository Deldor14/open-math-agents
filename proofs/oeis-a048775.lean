import OMAStatements.S_oeis_a048775
import Mathlib

open OMA.S_oeis_a048775
namespace Deldor14.IntervalMaps

private def b (n : ℕ) : ℤ := (2*n+1).choose (n+1)

private theorem twice (n : ℕ) : ((n+1).centralBinom:ℤ)=2*b n := by
  have symm : (2*n+1).choose n=(2*n+1).choose (n+1) := by
    simpa [show 2*n+1-n=n+1 by omega] using (Nat.choose_symm (show n≤2*n+1 by omega)).symm
  unfold b
  rw [Nat.centralBinom_eq_two_mul_choose,show 2*(n+1)=(2*n+1)+1 by omega,
    Nat.choose_succ_succ,symm]
  push_cast; ring

private theorem oneStep (n : ℕ) : ((n:ℤ)+2)*b (n+1)=(4*n+6)*b n := by
  have central :=  Nat.succ_mul_centralBinom_succ (n+1)
  have cast : (((n+1+1)*((n+1+1).centralBinom):ℕ):ℤ)=
      ((2*(2*(n+1)+1)*((n+1).centralBinom):ℕ):ℤ) := by exact_mod_cast central
  push_cast at cast
  rw [twice (n+1),twice n] at cast
  linarith

theorem result : type_of% @OMA.S_oeis_a048775.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+5 := ⟨n-5,by omega⟩
  have shift (m : ℕ) : a m=b m-((m:ℤ)+1) := rfl
  simp only [show k+5-1=k+4 by omega,show k+5-2=k+3 by omega,
    show k+5-3=k+2 by omega,show k+5-4=k+1 by omega,shift,Nat.cast_add,Nat.cast_ofNat]
  have h1 := oneStep (k+1)
  have h2 := oneStep (k+2)
  have h3 := oneStep (k+3)
  have h4 := oneStep (k+4)
  push_cast at h1 h2 h3 h4
  linear_combination h4-3*h3+3*h2-h1
end Deldor14.IntervalMaps

theorem OMA.solution : type_of% @OMA.S_oeis_a048775.main := Deldor14.IntervalMaps.result
