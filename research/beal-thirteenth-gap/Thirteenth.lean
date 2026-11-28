import Mathlib

namespace BealThirteenth

theorem symmetric_identity {R : Type*} [CommRing R] (a b : R) :
    4096 * (a^13 + b^13) = (a+b) * (
      (a+b)^12 + 78 * (a+b)^10 * (a-b)^2 + 715 * (a+b)^8 * (a-b)^4
      + 1716 * (a+b)^6 * (a-b)^6 + 1287 * (a+b)^4 * (a-b)^8
      + 286 * (a+b)^2 * (a-b)^10 + 13 * (a-b)^12) := by ring

/-- The six chord ratios give a lower bound for each individual chord. -/
theorem chord_lower (s : Fin 6 → ℝ) (u : ℝ)
    (hs : ∀ i, 0 ≤ s i) (ht : ∀ i, s i ≤ 2)
    (hn : 1 ≤ (∏ i, s i) * u^6) (i : Fin 6) :
    1 ≤ (32 * s i) * u^6 := by
  have hprod : ∏ j ∈ Finset.univ.erase i, s j ≤
      ∏ _j ∈ Finset.univ.erase i, (2:ℝ) :=
    Finset.prod_le_prod (fun j _ => hs j) (fun j _ => ht j)
  have hc : (Finset.univ.erase i).card = 5 := by simp
  simp only [Finset.prod_const, hc] at hprod
  have h := mul_le_mul_of_nonneg_left hprod (hs i)
  rw [Finset.mul_prod_erase _ _ (Finset.mem_univ i)] at h
  calc 1 ≤ (∏ j, s j) * u^6 := hn
       _ ≤ _ := by
         apply mul_le_mul_of_nonneg_right _ (by positivity)
         linarith

/-- Combine the lower chord norm with the small-arc and upper estimates. -/
theorem arc_bound (u h s e : ℝ) (p : ℕ) (hu : 0 < u)
    (hc : 1 ≤ (32*s)*u^6) (ha : (p:ℝ)*s ≤ 2*e)
    (hz : e*u^p ≤ 26*h) :
    (p:ℝ)*u^p ≤ 1664*h*u^6 := by
  calc (p:ℝ)*u^p ≤ ((p:ℝ)*u^p)*((32*s)*u^6) :=
         le_mul_of_one_le_right (by positivity) hc
       _ = ((p:ℝ)*s)*u^p*(32*u^6) := by ring
       _ ≤ (2*e)*u^p*(32*u^6) := by
         apply mul_le_mul_of_nonneg_right _ (by positivity)
         exact mul_le_mul_of_nonneg_right ha (by positivity)
       _ = (e*u^p)*(64*u^6) := by ring
       _ ≤ (26*h)*(64*u^6) := mul_le_mul_of_nonneg_right hz (by positivity)
       _ = _ := by ring

end BealThirteenth

#print axioms BealThirteenth.symmetric_identity
#print axioms BealThirteenth.chord_lower
#print axioms BealThirteenth.arc_bound
