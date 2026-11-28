import Mathlib

/-!
# Finite dual certificate for a potential-oscillation lower bound

A nonnegative tent weight transfers the nearest-neighbor inequalities to
first and second differences of the weight. This module checks the finite
summation and its constants independently of the geometric origin.
-/

open Finset

namespace Erdos142PotentialBarrier

/-- Fixed-height convexity and the antipodal progression force a positive cost. -/
theorem slice_deficit {l a r v κ : ℝ} (hv : v ≤ max l r) (ha : a ≤ max l r)
    (hk : 0 < κ) (hgap : r+κ/8 ≤ v) :
    κ/16 + |a-r|/2 ≤ 2*l-a-r := by
  rcases le_total l r with h | h
  · rw [max_eq_right h] at hv
    linarith
  · rw [max_eq_left h] at hv ha
    rcases le_total a r with h' | h'
    · rw [abs_of_nonpos (sub_nonpos.mpr h')]
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h')]
      linarith

private theorem shift_sum {G : Type*} [Fintype G] [AddCommGroup G]
    (w f : G → ℝ) (s : G) :
    (∑ i, w i*f (i+s)) = ∑ i, w (i-s)*f i := by
  classical
  let e := Equiv.addRight s
  have h := Equiv.sum_comp e (fun i => w (i-s)*f i)
  simpa [e] using h

/-- Signed residual inequality, also valid after centering the potential at any real level. -/
theorem weighted_residual {G : Type*} [Fintype G] [AddCommGroup G]
    (s : G) (w D R : G → ℝ) (κ : ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hrec : ∀ i, 0 < w i →
      κ/16+|D i|/2 ≤ D (i+s)-D i + R (i+s)-2*R i+R (i-s)) :
    (∑ i, w i)*(κ/16) ≤
      ∑ i, (max (|w (i-s)-w i|-w i/2) 0 * |D i| +
        (w (i-s)+w (i+s)-2*w i)*R i) := by
  classical
  let d i := w (i-s)-w i
  let b i := w (i-s)+w (i+s)-2*w i
  have rec_sum :
      (∑ i, w i*(κ/16+|D i|/2)) ≤
      ∑ i, w i*(D (i+s)-D i+R (i+s)-2*R i+R (i-s)) := by
    apply sum_le_sum
    intro i _
    rcases (hw i).eq_or_lt with hi | hi
    · simp [← hi]
    · exact mul_le_mul_of_nonneg_left (hrec i hi) (hw i)
  have parts :
      (∑ i, w i*(D (i+s)-D i+R (i+s)-2*R i+R (i-s))) =
      ∑ i, (d i*D i+b i*R i) := by
    have hback : (∑ i, w i*R (i-s)) = ∑ i, w (i+s)*R i := by
      simpa [sub_eq_add_neg] using shift_sum w R (-s)
    simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, shift_sum w D s,
      shift_sum w R s, hback, d, b, add_mul, sub_mul]
    simp_rw [show ∀ i, w i * (2*R i) = 2*w i*R i by intro i; ring]
    ring
  rw [parts] at rec_sum
  have point (i : G) :
      d i*D i+b i*R i ≤ w i*(|D i|/2) +
        (max (|d i|-w i/2) 0 * |D i|+b i*R i) := by
    have h₁ : d i*D i ≤ |d i| * |D i| := by rw [← abs_mul]; exact le_abs_self _
    have h₂ := mul_le_mul_of_nonneg_right (le_max_left (|d i|-w i/2) 0) (abs_nonneg (D i))
    linarith
  have integrated := rec_sum.trans (sum_le_sum (fun i _ => point i))
  simp only [mul_add, sum_add_distrib, ← sum_mul] at integrated
  change (∑ i, w i)*(κ/16) ≤ ∑ i, (max (|d i|-w i/2) 0 * |D i|+b i*R i)
  rw [sum_add_distrib]
  linarith

/-- The bound applies to a finite cyclic extension of a height grid. Off the
support of the weight no progression inequality is required. -/
theorem weighted_oscillation {G : Type*} [Fintype G] [AddCommGroup G]
    (s : G) (w D R : G → ℝ) (M κ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hM : 0 ≤ M) (hD : ∀ i, |D i| ≤ M)
    (hR : ∀ i, 0 ≤ R i ∧ R i ≤ M)
    (hrec : ∀ i, 0 < w i →
      κ/16+|D i|/2 ≤ D (i+s)-D i + R (i+s)-2*R i+R (i-s))
    (hslope : (∑ i, max (|w (i-s)-w i|-w i/2) 0) ≤ 3)
    (hlap : (∑ i, max (w (i-s)+w (i+s)-2*w i) 0) ≤ 2) :
    κ*(∑ i, w i) ≤ 80*M := by
  classical
  let d i := w (i-s)-w i
  let b i := w (i-s)+w (i+s)-2*w i
  have main := weighted_residual s w D R κ hw hrec
  have point (i : G) :
      max (|d i|-w i/2) 0 * |D i|+b i*R i ≤
        M*max (|d i|-w i/2) 0 + M*max (b i) 0 := by
    have h₁ := mul_le_mul_of_nonneg_left (hD i) (le_max_right (|d i|-w i/2) 0)
    have h₂ : b i*R i ≤ max (b i) 0 * M := by
      apply mul_le_mul _ (hR i).2 (hR i).1 (le_max_right _ _)
      exact le_max_left _ _
    linarith
  have integrated := main.trans (sum_le_sum (fun i _ => point i))
  simp only [sum_add_distrib, ← mul_sum] at integrated
  change (∑ i, max (|d i|-w i/2) 0) ≤ 3 at hslope
  change (∑ i, max (b i) 0) ≤ 2 at hlap
  nlinarith [mul_le_mul_of_nonneg_left hslope hM, mul_le_mul_of_nonneg_left hlap hM]

#print axioms slice_deficit
#print axioms weighted_residual
#print axioms weighted_oscillation

end Erdos142PotentialBarrier
