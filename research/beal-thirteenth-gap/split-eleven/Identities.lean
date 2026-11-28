import Mathlib

namespace Beal13.SplitEleven

theorem normalization {R : Type*} [CommRing R] (t s : R) :
    (2*t+3-(4-t^2)*s)^2 =
    (1-(4-t^2)*s)^2+4*((t+1)*(t+2))*(1-(2-t)*s) := by ring

theorem tangentWeight {R : Type*} [CommRing R] (t : R) :
    2*(4-t^2)-(2-t) = 6+t-2*t^2 := by ring

theorem tracedCoefficient :
    (9*6 + 5*(-1) + 4*11 + 8*31 + 10*(-16) : ZMod 11) = 5 := by decide

end Beal13.SplitEleven
