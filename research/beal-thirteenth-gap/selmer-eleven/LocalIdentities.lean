import Mathlib

namespace BealThirteenth.Eleven

/-- The quartic in the descent in the elementary symmetric coordinates. -/
theorem quartic {R : Type*} [CommRing R] (a b r : R) :
    a^4 + r*a^3*b + (r^2+r-1)*a^2*b^2 + r*a*b^3 + b^4 =
      (a+b)^4 + (r-4)*a*b*(a+b)^2 + (r^2-r+1)*(a*b)^2 := by ring

/-- The numerator that results from differentiating the equation at infinity. -/
theorem infinityDerivative {R : Type*} [CommRing R] (u t A : R)
    (h : u + t*u^6 = A*t^2*(1-u^11)) :
    t*(2*A*t*(1-u^11)-u^6) = u*(2+t*u^5) := by
  linear_combination -2*h

/-- The largest coordinates for a rank direction in the last dyadic check. -/
def spanWords : List Nat := [0,4273,10873,15048,16697,20872,27456,31729]
theorem finalDirection : 9362 ∉ spanWords := by decide

end BealThirteenth.Eleven
