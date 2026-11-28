import Mathlib.Tactic

namespace SepticEleven

/-- Multiplication of coordinates in the basis 1, θ, θ² modulo θ³+θ²-2θ-1. -/
structure Coordinates where
  a : ZMod 11
  b : ZMod 11
  c : ZMod 11
  deriving DecidableEq

def mul (x y : Coordinates) : Coordinates :=
  let h := x.b*y.c + x.c*y.b
  let k := x.c*y.c
  ⟨x.a*y.a+h-k, x.a*y.b+x.b*y.a+2*h-k, x.a*y.c+x.b*y.b+x.c*y.a-h+3*k⟩

def pow (x : Coordinates) : ℕ → Coordinates
  | 0 => ⟨1,0,0⟩
  | n+1 => mul (pow x n) x

def tr (x : Coordinates) : ZMod 11 := 3*x.a-x.b+5*x.c

/-- The two Frobenius preimages, tangent quotient and final trace. -/
theorem trace_obstruction :
    let d : Coordinates := ⟨10,10,2⟩
    let z : Coordinates := ⟨10,0,2⟩
    let w : Coordinates := ⟨10,4,0⟩
    pow d 11 = ⟨2,3,1⟩ ∧ pow z 11 = ⟨3,2,0⟩ ∧
    mul (pow z 3) w = mul ⟨6,1,9⟩ d ∧ tr w = 4 := by decide +kernel

/-- Irreducibility of the defining cubic follows from the absence of a root. -/
theorem cubic_no_root : ∀ t : ZMod 11, t^3+t^2-2*t-1 ≠ 0 := by decide +kernel

/-- The characteristic-zero identity used to construct the point on the curve. -/
theorem curve_identity (t S : ℤ) :
    (2*t+3-(4-t^2)*S)^2 = (1-(4-t^2)*S)^2 + 4*(t+1)*(t+2)*(1-(2-t)*S) := by ring

end SepticEleven
