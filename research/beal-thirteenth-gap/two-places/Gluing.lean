import Mathlib

namespace Beal13.TwoPlaces

theorem equalOffsets {K : Type*} [Field K] (q t u : K) (hq : q ≠ 0)
    (h : t*q + u*(-q) = 0) : t = u := by
  have h' : (t-u)*q = 0 := by linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hq)

theorem genusEightTest : (7 + 10 : ZMod 17) = 0 ∧ (7 : ZMod 17) ≠ 0 ∧
    (3 : ZMod 17) ≠ 0 := by decide

theorem genusElevenTest : (9 + 14 : ZMod 23) = 0 ∧ (9 : ZMod 23) ≠ 0 ∧
    (17 : ZMod 23) ≠ 0 := by decide

end Beal13.TwoPlaces
