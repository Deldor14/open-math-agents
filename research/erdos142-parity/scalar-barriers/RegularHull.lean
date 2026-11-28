import Mathlib.Tactic

/-! Finite convex mixtures of a nonnegative graph on the positive ray.
The product ab and position (2x-1)y are affine in either input separately. -/

namespace Erdos142RegularHull

inductive Mix (f : ℝ → ℝ) : ℝ → ℝ → Prop
  | leaf {x a : ℝ} (hx : 1 ≤ x) (ha : 0 ≤ a) (h : a ≤ f x) : Mix f x a
  | blend {x a y b : ℝ} (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1)
      (left : Mix f x a) (right : Mix f y b) :
      Mix f (u*x+(1-u)*y) (u*a+(1-u)*b)

theorem affine_transfer {f : ℝ → ℝ} {L B r : ℝ}
    (points : ∀ x a, 1 ≤ x → 0 ≤ a → a ≤ f x → Mix f (L*x+B) (r*a))
    {x a : ℝ} (h : Mix f x a) : Mix f (L*x+B) (r*a) := by
  induction h with
  | leaf hx ha hv => exact points _ _ hx ha hv
  | @blend x a y b u hu hu' _ _ ih jh =>
    convert Mix.blend u hu hu' ih jh using 1 <;> ring

theorem digit_transfer {f : ℝ → ℝ} (nonneg : ∀ x, 1 ≤ x → 0 ≤ f x)
    (digit : ∀ x y, 1 ≤ x → 1 ≤ y → f x*f y ≤ f ((2*x-1)*y))
    {x a y b : ℝ} (left : Mix f x a) (right : Mix f y b) :
    Mix f ((2*x-1)*y) (a*b) := by
  have fixed : ∀ x a, 1 ≤ x → 0 ≤ a → a ≤ f x →
      Mix f ((2*x-1)*y) (a*b) := by
    intro t s ht hs cap
    have pts : ∀ v d, 1 ≤ v → 0 ≤ d → d ≤ f v →
        Mix f ((2*t-1)*v+0) (s*d) := by
      intro v d hv hd bound
      rw [add_zero]
      exact Mix.leaf (one_le_mul_of_one_le_of_one_le (by linarith) hv)
        (mul_nonneg hs hd) ((mul_le_mul cap bound hd (nonneg _ ht)).trans (digit _ _ ht hv))
    simpa using affine_transfer pts right
  have pts : ∀ t s, 1 ≤ t → 0 ≤ s → s ≤ f t → Mix f ((2*y)*t + (-y)) (b*s) := by
    intro t s ht hs cap
    convert fixed t s ht hs cap using 1 <;> ring
  convert affine_transfer pts left using 1 <;> ring

/-- The argument used to concatenate the two changes in the log multiplier.
The hypothesis is the decreasing-increments property of a concave cost. -/
theorem split_cost {w : ℝ → ℝ}
    (decr : ∀ a b h, 0 ≤ a → a ≤ b → 0 ≤ h → w (b+h)-w b ≤ w (a+h)-w a)
    {A B D s t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAD : A ≤ D) (hBD : B ≤ D)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    w (D+s+t)-w D ≤ (w (A+s)-w A)+(w (B+t)-w B) := by
  linarith [decr A D s hA hAD hs, decr B (D+s) t hB (by linarith) ht]

/-- Transferring the product of two smaller digit witnesses to the target
length allows a scaled intermediate point with exactly multiplied ratios. -/
theorem source_product {x y m n : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hm : 1 ≤ m) :
    (2*x-1)*y ≤ x*y*(2-1/(x*m)) ∧
    (x*y*(2-1/(x*m)))*(m*n) = (2*(x*m)-1)*(y*n) ∧
    x ≤ x*y*(2-1/(x*m)) ∧ y ≤ x*y*(2-1/(x*m)) := by
  have xp : 0 < x := by linarith
  have mp : 0 < m := by linarith
  have yp : 0 < y := by linarith
  have p : 0 < x*m := mul_pos xp mp
  have xm : 1 ≤ x*m := one_le_mul_of_one_le_of_one_le hx hm
  have fac : 1 ≤ 2-1/(x*m) := by
    have := (div_le_one p).mpr xm
    linarith
  have xy : 1 ≤ x*y := one_le_mul_of_one_le_of_one_le hx hy
  have comp : x*y ≤ x*y*(2-1/(x*m)) := by
    simpa using mul_le_mul_of_nonneg_left fac (le_of_lt (mul_pos xp yp))
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (mul_nonneg xp.le yp.le)]
  · field_simp
  · exact (by nlinarith [mul_nonneg xp.le (sub_nonneg.mpr hy)] : x ≤ x*y).trans comp
  · exact (by nlinarith [mul_nonneg yp.le (sub_nonneg.mpr hx)] : y ≤ x*y).trans comp

#print axioms affine_transfer
#print axioms digit_transfer
#print axioms split_cost
#print axioms source_product

end Erdos142RegularHull
