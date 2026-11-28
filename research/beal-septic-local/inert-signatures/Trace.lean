import Mathlib.Tactic

namespace SepticInert

def W {R : Type*} [CommRing R] (x : R) : R := 6+x-2*x^2

theorem trace_numerators {R : Type*} [CommRing R] (x : R)
    (h : x^3+x^2-2*x-1=0) :
    (5+2*x-4*x^2)*(2*x+3)^3=7*W x*(x+1)*(x+2) ∧
    (-4-3*x+6*x^2)*(2*x+3)^3=7*W (x^2-2)*(x+1)*(x+2) ∧
    (-1-6*x+5*x^2)*(2*x+3)^3=7*W (1-x-x^2)*(x+1)*(x+2) := by
  unfold W
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-32*x^2-82*x-51)*h
  · linear_combination (14*x^3+76*x^2+109*x+52)*h
  · linear_combination (14*x^3+96*x^2+169*x+97)*h

theorem traces :
    (3*5-2+5*(-4):ℤ)=7*(-1) ∧
    (3*(-4)-(-3)+5*6:ℤ)=7*3 ∧
    (3*(-1)-(-6)+5*5:ℤ)=7*4 := by norm_num

theorem entry_identity (a b : ℤ) :
    (a+b)^6-(a^6-a^5*b+a^4*b^2-a^3*b^3+a^2*b^4-a*b^5+b^6)=
    7*a*b*(a^2+a*b+b^2)^2 := by ring

end SepticInert
