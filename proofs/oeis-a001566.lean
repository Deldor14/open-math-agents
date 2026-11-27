import OMAStatements.S_oeis_a001566
import Mathlib

open OMA.S_oeis_a001566
namespace Deldor14.McGarvey

/-- At index ten, the positive quotient formed with 40 as in the listed examples
and the one formed with 8 as in the printed formula are both multiples of 19². -/
theorem witnesses :
    0 < (term 10-7)/40 ∧ 19^2 ∣ (term 10-7)/40 ∧
    0 < a 10 ∧ 19^2 ∣ a 10 := by decide +kernel

end Deldor14.McGarvey

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a001566.main) := by
  intro hyp
  exact hyp.1 10 (by decide) 19 (by decide) Deldor14.McGarvey.witnesses.2.2.2
