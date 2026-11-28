import Mathlib.Tactic

namespace Erdos142LocalTransfer

/-- The local reserve past a completed plateau is exactly affine. -/
theorem affine_tail (u a b : ℝ) :
    2*((u-a)^2-(u-b)^2)+4*(b-a)*(u-(a+b)/2)=8*(b-a)*(u-(a+b)/2) := by ring

/-- The determinant identity for the retained half Hessian of a perspective.
    The tent slope may be either sign. -/
theorem determinant (D g x w k gamma slope : ℝ) (hD : D=1-g*x^2) (hne : D≠0)
    (hs : slope^2=1) :
    (gamma+k*slope^2/D)*(k*w^2*(4*g^2*x^2/D^3+g/D^2))
       -(2*k*w*slope*g*x/D^2)^2 =
    w^2*k*g*(k+gamma+3*gamma*g*x^2)/D^3 := by
  rw [show (2*k*w*slope*g*x/D^2)^2 = slope^2*(2*k*w*g*x/D^2)^2 by ring, hs]
  field_simp
  rw [hD]
  ring

end Erdos142LocalTransfer
#print axioms Erdos142LocalTransfer.affine_tail
#print axioms Erdos142LocalTransfer.determinant
