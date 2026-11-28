import RegularHull

namespace Erdos142CenteredProducts

open Erdos142RegularHull

def span (x y : ℝ) := x*y+(x-1)*(y-1)

theorem digit_transfer {f : ℝ → ℝ} (nonneg : ∀ x, 1 ≤ x → 0 ≤ f x)
    (digit : ∀ x y, 1 ≤ x → 1 ≤ y → f x*f y ≤ f (span x y))
    {x a y b : ℝ} (left : Mix f x a) (right : Mix f y b) :
    Mix f (span x y) (a*b) := by
  have fixed : ∀ t s, 1 ≤ t → 0 ≤ s → s ≤ f t → Mix f (span t y) (s*b) := by
    intro t s ht hs cap
    have pts : ∀ v d, 1 ≤ v → 0 ≤ d → d ≤ f v →
        Mix f ((2*t-1)*v + (1-t)) (s*d) := by
      intro v d hv hd bound
      rw [show (2*t-1)*v+(1-t)=span t v by unfold span; ring]
      apply Mix.leaf _ (mul_nonneg hs hd) ((mul_le_mul cap bound hd (nonneg _ ht)).trans (digit _ _ ht hv))
      unfold span
      linarith [one_le_mul_of_one_le_of_one_le ht hv,
        mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hv)]
    convert affine_transfer pts right using 1
    unfold span
    ring
  have pts : ∀ t s, 1 ≤ t → 0 ≤ s → s ≤ f t → Mix f ((2*y-1)*t+(1-y)) (b*s) := by
    intro t s ht hs cap
    convert fixed t s ht hs cap using 1 <;> (try unfold span) <;> ring
  convert affine_transfer pts left using 1 <;> (try unfold span) <;> ring

/-- Scaling up each digit increases the span per unit of product. -/
theorem scaled_span {u v m n : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    span u v * (m*n) ≤ span (u*m) (v*n) := by
  have hp : 0 ≤ (u-1)*m := mul_nonneg (by linarith) (by linarith)
  have hq : 0 ≤ (v-1)*n := mul_nonneg (by linarith) (by linarith)
  have first : (u-1)*m ≤ u*m-1 := by nlinarith
  have second : (v-1)*n ≤ v*n-1 := by nlinarith
  have both := mul_le_mul first second hq (hp.trans first)
  unfold span
  nlinarith only [both]

#print axioms digit_transfer
#print axioms scaled_span
end Erdos142CenteredProducts
