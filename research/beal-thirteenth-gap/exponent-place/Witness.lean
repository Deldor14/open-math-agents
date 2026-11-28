import Mathlib

namespace Beal13.ExponentPlace

def trRows : List (List Int) :=
  [[0,0,-8,8,16,-8], [-12,0,12,-8,12,0],
   [-4,24,12,0,-4,-24], [40,0,16,24,0,16]]

theorem distinguished (i j : Fin 6) (h : i ≠ j) :
    ∃ row ∈ trRows, (row[i.val]? = some 0) ≠ (row[j.val]? = some 0) := by
  fin_cases i <;> fin_cases j <;> first | exact False.elim (h rfl) | decide

theorem frobeniusSlope {R : Type*} [CommRing R] (a z w : R) :
    (a+(1-a)*z)*(1-w) - (a+(1-a)*w)*(1-z) = z-w := by ring

theorem squaredTrace {R : Type*} [CommRing R] (a b : R) :
    (a+b)^2-2*(a*b) = a^2+b^2 := by ring

end Beal13.ExponentPlace
