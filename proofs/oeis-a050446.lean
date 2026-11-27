import OMAStatements.S_oeis_a050446
import Mathlib

open OMA.S_oeis_a050446

/-- For two edges and magic sum one there are three labelings.
The one-letter alphabet supplies just one word of length two. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a050446.main) := by
  intro h
  have table : tableValue 2 1 = 3 := by decide +kernel
  have words : wordCount 2 1 = 1 := by decide +kernel
  have eq := h 2 1
  omega
