import Mathlib.Tactic

namespace Erdos142GraphTransfer

theorem reciprocal_tangent (d x : ℝ) (hd : 0 ≤ d) (hx : 0 ≤ x) :
    (1+2*x-d)/(1+x)^2 ≤ 1/(1+d) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [sq_nonneg (x-d)]

theorem one_vertex (d p : ℝ) (hd : 0 ≤ d) (hp : 0 ≤ p) :
    (1+2*d*p)/(1+d*p)^2*p - 1/(1+d*p)^2*d*p^2 = p/(1+d*p) := by
  have hn : 1+d*p ≠ 0 := by positivity
  field_simp
  ring

theorem positive_cost (d p : ℝ) (hd : 0 ≤ d) (hp : 0 ≤ p) :
    (1+2*d*p)/(1+d*p)^2*p ≤ 2*(p/(1+d*p)) := by
  have hs : 0 < 1+d*p := by positivity
  field_simp
  nlinarith [mul_nonneg hp (mul_nonneg hd hp)]

end Erdos142GraphTransfer
#print axioms Erdos142GraphTransfer.reciprocal_tangent
#print axioms Erdos142GraphTransfer.one_vertex
#print axioms Erdos142GraphTransfer.positive_cost
