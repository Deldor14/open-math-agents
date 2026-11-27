import OMAStatements.S_oeis_a113249
import Mathlib

namespace Deldor14.OddSquares
open OMA.S_oeis_a113249

private def root (m : ℕ) : ℕ → ℤ
  | 0 => 2
  | 1 => 8-(m:ℤ)^2
  | n+2 => 4*root m (n+1)-(m:ℤ)^2*root m n

private theorem everyOther (m j : ℕ) :
    a m (j+6)=(16-(m:ℤ)^2)*a m (j+4)-(m:ℤ)^2*(16-(m:ℤ)^2)*a m (j+2)+(m:ℤ)^6*a m j := by
  have advance (j : ℕ) : a m (j+4)=(m:ℤ)^4*a m j+(2*(m:ℤ))^2*a m (j+1)-4*a m (j+3) := rfl
  have e₁ : a m (j+5)=(m:ℤ)^4*a m (j+1)+(2*(m:ℤ))^2*a m (j+2)-4*a m (j+4) := advance (j+1)
  have e₂ : a m (j+6)=(m:ℤ)^4*a m (j+2)+(2*(m:ℤ))^2*a m (j+3)-4*a m (j+5) := advance (j+2)
  rw [e₂,e₁,advance j]
  ring

private theorem squared (m n : ℕ) : (root m (n+3))^2 =
    (16-(m:ℤ)^2)*(root m (n+2))^2-(m:ℤ)^2*(16-(m:ℤ)^2)*(root m (n+1))^2+(m:ℤ)^6*(root m n)^2 := by
  have advance (j : ℕ) : root m (j+2)=4*root m (j+1)-(m:ℤ)^2*root m j := rfl
  have e : root m (n+3)=4*root m (n+2)-(m:ℤ)^2*root m (n+1) := advance (n+1)
  rw [e,advance n]
  ring

private theorem found (m n : ℕ) : a m (2*n+1)=(root m n)^2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n<3
    · interval_cases n <;> norm_num [a,root] <;> ring
    · obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
      rw [show 2*(k+3)+1=(2*k+1)+6 by omega,everyOther,squared,
        show 2*k+1+4=2*(k+2)+1 by omega,show 2*k+1+2=2*(k+1)+1 by omega,
        ih (k+2) (by omega),ih (k+1) (by omega),ih k (by omega)]

theorem result : type_of% @OMA.S_oeis_a113249.main := by
  intro m n
  exact ⟨root m n, by rw [found,pow_two]⟩
end Deldor14.OddSquares
theorem OMA.solution : type_of% @OMA.S_oeis_a113249.main := Deldor14.OddSquares.result
