import OMAStatements.S_oeis_a248231
import Mathlib

/-! Formalization of Ridouane Oudra’s formula for the tails of the zeta series at 5. The lower and upper reciprocal-square barriers telescope. The arithmetic threshold follows from the fact that a square cannot be two modulo four. -/
namespace Deldor14.ZetaTail
open Filter Finset OMA.S_oeis_a248231
open scoped Topology
private noncomputable def W (d : ℝ) (k : ℕ) := 1 / (2*(k:ℝ)^2+2*k+d)^2
private theorem estimate (k : ℕ) (hk : 1 ≤ k) :
    W 2 k-W 2 (k+1)<term k ∧ term k<W 1 k-W 1 (k+1) := by
  let x : ℝ := k
  have hx : 1 ≤ x := by dsimp [x];exact_mod_cast hk
  have h0 : 0 < x+1 := by linarith
  have pos (d : ℝ) (hd : 0 < d) (v : ℝ) (hv : 0≤v) : 0<2*v^2+2*v+d := by positivity
  dsimp [W,term]
  push_cast
  change 1/(2*x^2+2*x+2)^2-1/(2*(x+1)^2+2*(x+1)+2)^2<1/(x+1)^5 ∧
    1/(x+1)^5<1/(2*x^2+2*x+1)^2-1/(2*(x+1)^2+2*(x+1)+1)^2
  constructor
  · have hp := pos 2 (by norm_num) x (by linarith)
    have hq := pos 2 (by norm_num) (x+1) h0.le
    field_simp
    ring_nf
    nlinarith [show 0≤x^2 by positivity,show 0≤x^3 by positivity,show 0≤x^4 by positivity,
      show 0≤x^5 by positivity,show 0≤x^6 by positivity]
  · have hp := pos 1 (by norm_num) x (by linarith)
    have hq := pos 1 (by norm_num) (x+1) h0.le
    field_simp
    ring_nf
    nlinarith [show 0≤x^2 by positivity,show 0≤x^3 by positivity,show 0≤x^4 by positivity,
      show 0≤x^5 by positivity,show 0≤x^6 by positivity]
private theorem telescope (d : ℝ) (hd : 1 ≤ d) (k : ℕ) :
    HasSum (fun j : ℕ => W d (k+j)-W d (k+j+1)) (W d k) := by
  have dec (j : ℕ) : W d (k+j+1)≤W d (k+j) := by
    dsimp [W]
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    nlinarith [show (0:ℝ) ≤ k by positivity,show (0:ℝ) ≤ j by positivity]
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun j => sub_nonneg.mpr (dec j)) _).mpr
  have seq (N : ℕ) : ∑ j ∈ range N, (W d (k+j)-W d (k+j+1)) = W d k-W d (k+N) := by
    induction N with
    | zero => simp
    | succ N ih => rw [sum_range_succ,ih]; simp only [Nat.add_succ];ring
  simp_rw [seq]
  have aug : Tendsto (fun j : ℕ => (2*((k+j:ℕ):ℝ)^2+2*(k+j:ℕ)+d)^2) atTop atTop := by
    apply tendsto_atTop_mono (f:=fun j : ℕ => (j:ℝ)) _ tendsto_natCast_atTop_atTop
    intro j
    push_cast
    have h : (j:ℝ)+1 ≤ 2*((k:ℝ)+j)^2+2*((k:ℝ)+j)+d := by nlinarith [sq_nonneg ((k:ℝ)+j), show (0:ℝ) ≤ k by positivity,show (0:ℝ) ≤ j by positivity]
    nlinarith [sq_nonneg (2*((k:ℝ)+j)^2+2*((k:ℝ)+j)+d-1),show (0:ℝ) ≤ j by positivity]
  have zero : Tendsto (fun j : ℕ => W d (k+j)) atTop (𝓝 0) := by simpa [Function.comp_def,W,one_div,inv_pow] using tendsto_inv_atTop_zero.comp aug
  simpa only [sub_zero] using (tendsto_const_nhds (x:=W d k)).sub zero
private theorem sandwich (k : ℕ) (hk : 1 ≤ k) : W 2 k < tail k ∧ tail k < W 1 k := by
  have l := telescope 2 (by norm_num) k
  have u := telescope 1 (by norm_num) k
  have e (j : ℕ) := estimate (k+j) (by omega)
  have sum : Summable (fun j : ℕ => term (k+j)) :=
    .of_nonneg_of_le (fun _ => by dsimp [term];positivity) (fun j => (e j).2.le) u.summable
  rw [←l.tsum_eq,←u.tsum_eq,tail]
  exact ⟨l.summable.tsum_lt_tsum (i:=0) (fun j => (e j).1.le) (e 0).1 sum,
    sum.tsum_lt_tsum (i:=0) (fun j => (e j).2.le) (e 0).2 u.summable⟩
end Deldor14.ZetaTail

namespace Deldor14.ZetaTail
open OMA.S_oeis_a248231
private theorem threshold (n k : ℕ) (hn : 1 < n) :
    proposal n ≤ k ↔ n^2 ≤ 2*k^2+2*k+1 := by
  have ns : n^2 ≠ 2*k^2+2*k+2 := by
    have finite : ∀ a b : ZMod 4, a^2 ≠ 2*b^2+2*b+2 := by decide +kernel
    intro eq
    apply finite n k
    exact_mod_cast congrArg (fun v : ℕ => (v:ZMod 4)) eq
  have enough : 4 ≤ 2*n^2 := by nlinarith
  have sub := Nat.sub_add_cancel enough
  calc
    _ ↔ Nat.sqrt (2*n^2-4)<2*k+1 := by unfold proposal;omega
    _ ↔ 2*n^2-4 < (2*k+1)^2 := Nat.sqrt_lt'
    _ ↔ _ := by
      ring_nf at ns sub ⊢
      omega

private theorem cutoff (n k : ℕ) (hn : 1<n) (hk : 0<k) :
    tail k < 1/(n:ℝ)^4 ↔ n^2 ≤ 2*k^2+2*k+1 := by
  obtain ⟨lo,hi⟩ := sandwich k hk
  have hn' : 0 < (n:ℝ)^2 := by positivity
  have hpow : (n:ℝ)^4=((n:ℝ)^2)^2 := by ring
  rw [hpow]
  constructor
  · intro small
    by_contra! big
    have higher : 2*(k:ℝ)^2+2*k+2 ≤ (n:ℝ)^2 := by exact_mod_cast (show 2*k^2+2*k+2 ≤ n^2 by omega)
    have le : 1/((n:ℝ)^2)^2 ≤ W 2 k := by
      dsimp [W]
      apply one_div_le_one_div_of_le (by positivity)
      gcongr
    exact (not_lt_of_ge le) (lo.trans small)
  · intro h
    have le : (n:ℝ)^2 ≤ 2*(k:ℝ)^2+2*k+1 := by exact_mod_cast h
    refine hi.trans_le ?_
    dsimp [W]
    apply one_div_le_one_div_of_le (by positivity)
    gcongr

theorem full : type_of% @OMA.S_oeis_a248231.main := by
  intro n hn
  have pos : 0 < proposal n := by
    by_contra! h
    have e := (threshold n 0 hn).mp h
    simp only [zero_pow (by decide : 2≠0),mul_zero,zero_add] at e
    nlinarith
  refine ⟨⟨pos,(cutoff n _ hn pos).mpr ((threshold n _ hn).mp le_rfl)⟩,?_⟩
  intro k hk
  exact (threshold n k hn).mpr ((cutoff n k hn hk.1).mp hk.2)

end Deldor14.ZetaTail

theorem OMA.solution : type_of% @OMA.S_oeis_a248231.main := Deldor14.ZetaTail.full
