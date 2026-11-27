import OMAStatements.S_oeis_a241884
import Mathlib

/-- Robert Israel's counterexample in the OEIS entry. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a241884.main) := by
  intro conjecture
  have term := (conjecture 56 (by decide)).mpr (by decide +kernel)
  exact term 7 (by decide +kernel) ⟨7, by decide, by norm_num⟩
