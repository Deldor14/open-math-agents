import OMAStatements.S_oeis_a373163
import Mathlib

open Real Finset OMA.S_oeis_a373163
namespace Deldor14.Cosine

noncomputable def term (r : ℝ) (k : ℕ) : ℝ := Real.cos (2*(k:ℝ)*Real.pi/3)*r^k

theorem cycle (r : ℝ) (k : ℕ) : term r (k+3)=term r k*r^3 := by
  unfold term
  push_cast
  rw [show 2*((k:ℝ)+3)*π/3 = 2*(k:ℝ)*π/3 + 2*π by ring,cos_add_two_pi,pow_add]
  ring

theorem cos1 : Real.cos (2*π/3) = -(1/2:ℝ) := by
  rw [show 2*π/3=2*(π/3) by ring,cos_two_mul,cos_pi_div_three]
  norm_num

theorem cos2 : Real.cos (4*π/3) = -(1/2:ℝ) := by
  rw [show 4*π/3=2*(2*π/3) by ring,cos_two_mul,cos1]
  norm_num

theorem identity (r : ℝ) (hr : 0≤r) (h1 : r<1) :
    (1-r^3)*(∑' k,term r k)=1-r/2-r^2/2 := by
  have su : Summable (term r) := by
    apply (summable_geometric_of_lt_one hr h1).of_norm_bounded
    intro k
    rw [term, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr k)]
    exact mul_le_of_le_one_left (pow_nonneg hr k) (Real.abs_cos_le_one _)
  have h := su.sum_add_tsum_nat_add 3
  simp only [cycle,tsum_mul_right] at h
  have first : ∑ k ∈ range 3, term r k = 1-r/2-r^2/2 := by
    norm_num [sum_range_succ,term,cos1,cos2] <;> ring
  rw [first] at h
  linarith

theorem asSeries (n : ℕ) : fraction n = ∑' k, term (1/(n:ℝ)) k := by
  unfold fraction term
  simp [one_div,div_eq_mul_inv]

end Deldor14.Cosine
open Deldor14.Cosine

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a373163.main) := by
  intro h
  have h2 := identity (1/2) (by norm_num) (by norm_num)
  have h3 := identity (1/3) (by norm_num) (by norm_num)
  have bad := h 1 2 (by decide)
  change 0 ≤ (-1:ℝ)^1 * (fraction 3-fraction 2) at bad
  rw [asSeries,asSeries] at bad
  norm_num at h2 h3 bad
  linarith
