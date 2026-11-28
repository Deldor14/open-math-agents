import Mathlib.Tactic

namespace Erdos142Compression

/-- Each of two intersections of convex hulls is covered by the same hole budget.
The two cuts in the interval replacement cost half the respective overlaps. -/
theorem trim_budget (p P n M h : ℝ) (hh : 0 ≤ h)
    (h₁ : M-p-2*n ≤ h) (h₂ : M+2*P-1-p ≤ h) :
    P-p+M-n-h ≤ min P ((1-M+p)/2) - p + M - max n ((M-p)/2) := by
  rw [min_def,max_def]
  split_ifs <;> linarith

/-- Mixed-sign midpoint obstructions after compression. -/
theorem cuts_admissible (p P n M : ℝ) :
    M ≤ p+2*(max n ((M-p)/2)) ∧
    M+2*(min P ((1-M+p)/2)) ≤ 1+p := by
  constructor
  · linarith [le_max_right n ((M-p)/2)]
  · linarith [min_le_right P ((1-M+p)/2)]

/-- The area of the optimal pair is a nondecreasing function of M-p. -/
theorem width_mono (l C d D : ℝ) (h : d ≤ D) :
    d + min C ((1-d)/2) - max l (d/2) ≤
    D + min C ((1-D)/2) - max l (D/2) := by
  simp only [min_def,max_def]
  split_ifs <;> linarith

#print axioms trim_budget
#print axioms cuts_admissible
#print axioms width_mono
end Erdos142Compression
