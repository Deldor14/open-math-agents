import Mathlib.Tactic

namespace Erdos142Weighted
open Finset

/-- An arbitrary admissible pattern is dominated by a single product of
mixtures, without enumerating the pattern vector in the direction search. -/
theorem selected_product {ι α : Type*} (I : Finset ι) (L : Finset α)
    (label : ι → α) (p : α → ℝ) (f : ι → α → ℝ)
    (mem : ∀ i∈I, label i∈L) (hp : ∀ j∈L, 0≤p j)
    (hf : ∀ i∈I, ∀ j∈L, 0≤f i j) :
    (∏ i∈I, p (label i))*(∏ i∈I, f i (label i)) ≤
      ∏ i∈I, ∑ j∈L, p j*f i j := by
  classical
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro i hi
    exact mul_nonneg (hp _ (mem _ hi)) (hf i hi _ (mem _ hi))
  · intro i hi
    exact Finset.single_le_sum (fun j hj => mul_nonneg (hp j hj) (hf i hi j hj)) (mem i hi)

/-- Quantitative assembly after combining the published base energy with
the perspective defect. g represents convex cost in the angular distance. -/
theorem strong_metric (K d t r g loss : ℝ) (hK : 0≤K) (hg : 0≤g)
    (hbound : g≤4*|d|+8*|r|)
    (henergy : 3*K*d^2/2 + 2*t^2 + K*r^2/2 ≤ loss) :
    K*d^2 + t^2 + K*g^2 ≤ 256*loss := by
  have h1 : g^2 ≤ (4*|d|+8*|r|)^2 := by gcongr
  have h2 : (4*|d|+8*|r|)^2 ≤ 32*d^2+128*r^2 := by
    nlinarith [sq_nonneg (4*|d|-8*|r|),sq_abs d,sq_abs r]
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hK
  nlinarith [mul_nonneg hK (sq_nonneg d),sq_nonneg t]

/-- Two branch averages are compared by cross multiplication even when the
scores themselves can be negative. -/
theorem half_average (x y a b : ℝ) (ha : 0<a) (hb : 0<b) (h : y*a≤x*b) :
    (x+y)/(a+b)≤x/a := by
  rw [div_le_div_iff₀ (by positivity) ha]
  nlinarith

#print axioms selected_product
#print axioms strong_metric
#print axioms half_average
end Erdos142Weighted
