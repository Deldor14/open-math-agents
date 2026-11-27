import OMAStatements.S_oeis_a000332
import Mathlib

open Filter PowerSeries
open scoped BigOperators Topology PowerSeries.WithPiTopology
namespace Deldor14.DigitProduct

noncomputable abbrev x : PowerSeries ℤ := X
noncomputable def blocks (b N : ℕ) : PowerSeries ℤ :=
  ∏ i ∈ Finset.range N, ∑ j ∈ Finset.range b, x ^ (j*b^i)

private theorem telescope (b N : ℕ) : blocks b N * (1-x) = 1-x^(b^N) := by
  induction N with
  | zero => simp [blocks]
  | succ N ih =>
    rw [blocks, Finset.prod_range_succ,← blocks]
    calc
      _ = (∑ j ∈ Finset.range b, x^(j*b^N))*(blocks b N*(1-x)) := by ring
      _ = (∑ j ∈ Finset.range b, (x^(b^N))^j)*(1-x^(b^N)) := by
        rw [ih]; simp_rw [← pow_mul, Nat.mul_comm (b^N)]
      _ = _ := by rw [geom_sum_mul_neg,← pow_mul,pow_succ]

private theorem tends (b : ℕ) (hb : 2 ≤ b) :
    Tendsto (blocks b) atTop (𝓝 (invOneSubPow ℤ 1).val) := by
  have zero : Tendsto (fun N : ℕ => x^(b^N)) atTop (𝓝 0) := by
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    refine tendsto_atTop_of_eventually_const (i₀ := d+1) ?_
    intro N hN
    have lower : N ≤ b^N := Nat.le_of_lt (Nat.lt_pow_self (by omega))
    simp [x,coeff_X_pow,show d ≠ b^N by omega]
  have inverse : (1-x)*(invOneSubPow ℤ 1).val=1 := by
    simpa only [invOneSubPow_inv_eq_one_sub_pow,pow_one,x] using (invOneSubPow ℤ 1).inv_val
  have exactBlock (N : ℕ) : blocks b N=(1-x^(b^N))*(invOneSubPow ℤ 1).val := by
    rw [← telescope, mul_assoc,inverse,mul_one]
  change Tendsto (fun N => blocks b N) _ _
  simp_rw [exactBlock]
  simpa using ((tendsto_const_nhds (x := (1 : PowerSeries ℤ))).sub zero).mul_const (invOneSubPow ℤ 1).val

theorem result (b : ℕ) (hb : 2 ≤ b) :
    Tendsto (fun N : ℕ => x * ∏ i ∈ Finset.range N,
      (∑ j ∈ Finset.range b,x^(j*b^i))^5) atTop (𝓝 (x*(invOneSubPow ℤ 5).val)) := by
  have powers : (invOneSubPow ℤ 1).val^5=(invOneSubPow ℤ 5).val := by
    simp [invOneSubPow_eq_inv_one_sub_pow]
  simpa only [blocks,Finset.prod_pow,powers] using (((tends b hb).pow 5).const_mul x)

end Deldor14.DigitProduct

theorem OMA.solution : type_of% @OMA.S_oeis_a000332.main := Deldor14.DigitProduct.result
