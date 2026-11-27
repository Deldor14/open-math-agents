import OMAStatements.S_oeis_a002822
import Mathlib

/-! At j = 63 the outer twin primes are 2267 and 2269, whereas
6j - 1 = 377 = 13 * 29. -/
namespace Deldor14.TwinPair
open OMA.S_oeis_a002822
theorem refute : ¬(type_of% @OMA.S_oeis_a002822.main) := by
  intro h
  have outer : InSeq (6*63) := by norm_num [InSeq]
  have inner := (h 63 (by decide) outer).2.1
  norm_num at inner
end Deldor14.TwinPair
theorem OMA.disproof : ¬(type_of% @OMA.S_oeis_a002822.main) := Deldor14.TwinPair.refute
