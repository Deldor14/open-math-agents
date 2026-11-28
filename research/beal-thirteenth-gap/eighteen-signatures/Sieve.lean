import Mathlib

namespace Beal13.ProjectiveSieve

theorem crossTerm {R : Type*} [CommRing R] (a b z w t k : R) :
    a*((t+k)+(1-(t+k))*w) - b*((t+k)+(1-(t+k))*z) =
      a*(t+(1-t)*w) - b*(t+(1-t)*z) + k*(a*(1-w)-b*(1-z)) := by ring

theorem twoFactors {R : Type*} [CommRing R] (h d s : R) :
    (2*h-1-h*d*s)^2 = (1-h*d*s)^2 + 4*h*(h-1)*(1-d*s) := by ring

theorem alternativePair {R : Type*} [CommRing R] (x : R) :
    (2-x)*(x+2) = 4-x^2 ∧ 2*(2-x)-(4-x^2)=x*(x-2) := by
  constructor <;> ring

end Beal13.ProjectiveSieve
