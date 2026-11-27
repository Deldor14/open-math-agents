import OMAStatements.S_mo_509920
import Mathlib

/-! At n=0 the catalogue asks for a total function from ℕ to the empty
type. The positive-n source theorem is true; Peter Taylor gives a merging
argument at https://mathoverflow.net/a/509921 and our separate certificate
proves the positive case by extracting each greatest Fibonacci summand. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_509920.main) := by
  intro h
  obtain ⟨g,_⟩ := h 0 ∅ (by simp) (by simp)
  have impossible := (g 0).isLt
  simpa using impossible
