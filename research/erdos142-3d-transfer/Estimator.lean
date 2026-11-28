import Mathlib.Tactic

namespace Erdos142EndpointExtraction

/-- Weighting a nonnegative continuation by an atomwise lower comparison. -/
theorem continue_lower {ι : Type*} (I : Finset ι) (p q f : ι → ℝ) (a : ℝ)
    (hp : ∀ i ∈ I, a * q i ≤ p i) (hf : ∀ i ∈ I, 0 ≤ f i) :
    a * ∑ i ∈ I, q i * f i ≤ ∑ i ∈ I, p i * f i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right (hp i hi) (hf i hi)

/-- The two signs in the pessimistic estimator have opposite one-step bounds. -/
theorem estimator_step (a b x y sx sy : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : a*x ≤ sx) (hy : sy ≤ b*y) :
    a^(k+1)*x - b^(k+1)*y ≤ a^k*sx - b^k*sy := by
  simpa [pow_succ, mul_assoc] using
    sub_le_sub (mul_le_mul_of_nonneg_left hx (pow_nonneg ha k))
      (mul_le_mul_of_nonneg_left hy (pow_nonneg hb k))

/-- At least one element attains the lower bound on an unnormalized finite average. -/
theorem choose_block {ι : Type*} (I : Finset ι) (hI : I.Nonempty) (f : ι → ℝ) (target : ℝ)
    (h : I.card * target ≤ ∑ i ∈ I, f i) : ∃ i ∈ I, target ≤ f i := by
  by_contra! hu
  have hh := Finset.sum_lt_sum_of_nonempty hI hu
  simp only [Finset.sum_const, nsmul_eq_mul] at hh
  linarith

end Erdos142EndpointExtraction
#print axioms Erdos142EndpointExtraction.continue_lower
#print axioms Erdos142EndpointExtraction.estimator_step
#print axioms Erdos142EndpointExtraction.choose_block
