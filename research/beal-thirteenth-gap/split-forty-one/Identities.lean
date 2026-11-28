import Mathlib

namespace Beal13.SplitFortyOne

theorem normalization {R : Type*} [CommRing R] (t s : R) :
    (2*t+3-(4-t^2)*s)^2 =
    (1-(4-t^2)*s)^2+4*((t+1)*(t+2))*(1-(2-t)*s) := by ring

theorem modularObstruction :
    (-11 : ZMod 41) ≠ -77 ∧ (-11 : ZMod 41) ≠ -17 := by decide

theorem boundaryTrace :
    (28*6 + 14*(-1) + 25*11 + 30*(-4) + 40*31 + 18*(-16) : ZMod 41) = 31 := by decide

theorem derivativeFactor : (-2 * 20 : ZMod 41) = 1 := by decide

end Beal13.SplitFortyOne
