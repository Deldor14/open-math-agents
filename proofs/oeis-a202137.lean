import OMAStatements.S_oeis_a202137
import Mathlib

/-! Put the entire run just above the square of 24M, with M a factorial.
An explicitly chosen small divisor of M divides each term of the block. -/
namespace Deldor14.CompositeRuns
open OMA.S_oeis_a202137
theorem full : type_of% @OMA.S_oeis_a202137.main := by
  intro L
  let B := 24*(L+1)+1
  let M := B.factorial
  have bpos : 0<B := by dsimp [B];omega
  have bM : B≤M := Nat.le_of_dvd (Nat.factorial_pos B) (Nat.dvd_factorial bpos le_rfl)
  refine ⟨24*M^2+1,?_⟩
  intro i hi
  let d:=24*(i+1)+1
  have dpos : 1<d := by dsimp [d];omega
  have dl : d≤B := by dsimp [d,B];omega
  have dM : d∣M := Nat.dvd_factorial (by omega) dl
  have id : 24*(24*M^2+1+i)+1=(24*M)^2+d := by dsimp [d];ring
  unfold IsTerm
  rw [id]
  constructor
  · rintro ⟨r,hr⟩
    rcases le_or_gt r (24*M) with h | h
    · nlinarith [Nat.mul_self_le_mul_self h]
    · have b := Nat.mul_self_le_mul_self (show 24*M+1≤r by omega)
      nlinarith
  · intro h
    have dvd : d ∣ (24*M)^2+d := dvd_add
      (dvd_pow (dM.trans (dvd_mul_left M 24)) (by decide : 2 ≠ 0)) (dvd_refl d)
    rcases (Nat.dvd_prime h).mp dvd with small | large
    · omega
    · have : 0<(24*M)^2 := by have : 0<M := Nat.factorial_pos B;positivity
      omega
end Deldor14.CompositeRuns
theorem OMA.solution : type_of% @OMA.S_oeis_a202137.main := Deldor14.CompositeRuns.full
