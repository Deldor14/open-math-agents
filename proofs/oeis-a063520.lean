import OMAStatements.S_oeis_a063520
import Mathlib

/-! Wilson's OEIS comment concerns the range of the counting sequence. The
catalogue translation instead asks about the indices at which it is positive.
The triple below shows that every positive index has a witness. -/
namespace Deldor14.SumDividesProduct
theorem all_indices (n : ℕ) (hn : 0<n) : ∃ r s t : ℕ,
    0 < t ∧ t ≤ s ∧ s ≤ r ∧ r * s * t = n * (r+s+t) := by
  refine ⟨n*(n+2),n+1,1,by decide,by omega,?_,by ring⟩
  nlinarith
theorem refute : ¬(type_of% @OMA.S_oeis_a063520.main) := by
  intro h
  exact ((h 2 (by decide)).mp (all_indices 2 (by decide))).1 rfl
end Deldor14.SumDividesProduct
theorem OMA.disproof : ¬(type_of% @OMA.S_oeis_a063520.main) := Deldor14.SumDividesProduct.refute
