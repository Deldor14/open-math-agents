import Mathlib

/-! Binomial cancellation for a finite family of real shifts and signed weights. -/

namespace Erdos142SignedScale
open Finset

/-- The signed moment of order j of a finite family of shifts. -/
noncomputable def moment {ι : Type*} (I : Finset ι) (w s : ι → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ I, w i * s i ^ j

/-- Vanishing of the first h moments removes every binomial term with j < h.
The sum on the right is empty when m < h. -/
theorem expansion {ι : Type*} (I : Finset ι) (w s : ι → ℝ) {h : ℕ}
    (cancel : ∀ j < h, moment I w s j = 0) (t : ℝ) (m : ℕ) :
    (∑ i ∈ I, w i * (t - s i)^m) =
      ∑ j ∈ Icc h m, (m.choose j : ℝ) * (-1)^j * moment I w s j * t^(m-j) := by
  let term (j : ℕ) := (m.choose j : ℝ) * (-1)^j * moment I w s j * t^(m-j)
  change _ = ∑ j ∈ Icc h m, term j
  calc
    _ = ∑ i ∈ I, ∑ j ∈ range (m+1), w i * ((-s i)^j * t^(m-j) * (m.choose j : ℝ)) := by
      apply sum_congr rfl
      intro i _
      rw [show t - s i = -s i + t by ring, add_pow, mul_sum]
    _ = ∑ j ∈ range (m+1), term j := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      unfold term moment
      rw [mul_sum, sum_mul]
      apply sum_congr rfl
      intro i _
      rw [neg_pow]
      ring
    _ = _ := by
      symm
      apply sum_subset
      · intro j hj
        exact mem_range.mpr (by have := (mem_Icc.mp hj).2; omega)
      · intro j hj hnot
        have jm := mem_range.mp hj
        have jh : j < h := by
          by_contra! hle
          exact hnot (mem_Icc.mpr ⟨hle, by omega⟩)
        simp [term, cancel j jh]

/-- At degree h the translated signed sum is independent of t. -/
theorem leading_term {ι : Type*} (I : Finset ι) (w s : ι → ℝ) {h : ℕ}
    (cancel : ∀ j < h, moment I w s j = 0) (t : ℝ) :
    (∑ i ∈ I, w i * (t - s i)^h) = (-1)^h * moment I w s h := by
  rw [expansion I w s cancel]
  simp

/-- Three equally spaced logarithmic scales with weights (1,-2,1).
Taking d=log 2 gives the dyadic stencil. -/
theorem stencil (r d t : ℝ) (m : ℕ) :
    (t-r)^m - 2*(t-(r+d))^m + (t-(r+2*d))^m =
      ∑ j ∈ Icc 2 m, (m.choose j : ℝ) * (-1)^j *
        (r^j - 2*(r+d)^j + (r+2*d)^j) * t^(m-j) := by
  let w : Fin 3 → ℝ := ![1,-2,1]
  let s : Fin 3 → ℝ := ![r,r+d,r+2*d]
  have mj (j : ℕ) : moment univ w s j = r^j - 2*(r+d)^j + (r+2*d)^j := by
    simp [moment, Fin.sum_univ_three, w, s]
    ring
  have zero (j : ℕ) (hj : j < 2) : moment univ w s j = 0 := by
    rw [mj]
    interval_cases j <;> ring
  have eq := expansion univ w s zero t m
  simp_rw [mj] at eq
  convert eq using 1
  simp [Fin.sum_univ_three, w, s]
  ring

/-- The second-degree dyadic stencil equals twice the square of the shift. -/
theorem stencil_quadratic (r d t : ℝ) :
    (t-r)^2 - 2*(t-(r+d))^2 + (t-(r+2*d))^2 = 2*d^2 := by ring

#print axioms expansion
#print axioms leading_term
#print axioms stencil
#print axioms stencil_quadratic

end Erdos142SignedScale
