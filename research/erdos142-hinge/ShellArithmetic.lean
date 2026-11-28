import Mathlib

namespace Erdos142Shell

/-- From the two directional scales to the determinant scale of one block. -/
theorem determinant_scale {s a d eta L : ℝ} (ha : 0 ≤ a)
    (he : 0 ≤ eta) (hL : 0 ≤ L) (hd : d^2 ≤ s*a)
    (h₁ : s ≤ L) (h₂ : a ≤ eta^2*L) : d ≤ eta*L := by
  have h := mul_le_mul h₁ h₂ ha hL
  nlinarith [mul_nonneg he hL, sq_nonneg (d-eta*L)]

/-- A uniform lower bound on the AM--GM scale after clipping large entries. -/
theorem clipping_log_budget {ι : Type*} [Fintype ι] (t v : ι → ℝ)
    (T : Finset ι) (B : ℝ) (hs : 0 ≤ ∑ i, t i)
    (hbig : ∀ i ∈ T, t i - v i ≤ B)
    (hsmall : ∀ i ∉ T, t i = v i) :
    -(T.card:ℝ)*B ≤ ∑ i, v i := by
  classical
  have h : ∀ i : ι, t i - v i ≤ if i ∈ T then B else 0 := by
    intro i
    by_cases hi : i ∈ T
    · simpa [hi] using hbig i hi
    · simp [hi, hsmall i hi]
  have hz := Finset.sum_le_sum (s:=Finset.univ) fun i _ => h i
  rw [Finset.sum_sub_distrib] at hz
  have ht : (∑ i, if i ∈ T then B else (0:ℝ)) = T.card * B := by
    simp
  rw [ht] at hz
  linarith

/-- Direct weighted exponential-moment bound for independent Bernoulli choices.
The factors on the left are the one-coordinate Laplace transforms. -/
theorem laplace_product {ι : Type*} [Fintype ι] (w : ι → ℝ) (delta k : ℝ)
    (h₀ : ∀ i, 0 ≤ 1-delta+delta*Real.exp (-w i))
    (hsec : ∀ i, 1-delta+delta*Real.exp (-w i) ≤ 1-k*w i) :
    (∏ i, (1-delta+delta*Real.exp (-w i))) ≤ Real.exp (-k*∑ i, w i) := by
  calc
    _ ≤ ∏ i, Real.exp (-k*w i) := by
      apply Finset.prod_le_prod (fun i _ => h₀ i)
      intro i _
      exact (hsec i).trans (by linarith [Real.add_one_le_exp (-k*w i)])
    _ = _ := by rw [← Real.exp_sum, Finset.mul_sum]

#print axioms determinant_scale
#print axioms clipping_log_budget
#print axioms laplace_product
end Erdos142Shell
