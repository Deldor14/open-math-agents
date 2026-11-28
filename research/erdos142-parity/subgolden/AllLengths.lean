import ExactRoth
import ShortPrefixGrowth
import Mathlib.NumberTheory.Real.GoldenRatio

/-! A positive relative gain with upward rounding, at every integer length. -/
namespace Erdos142AllLengths
open Erdos142ExactGrid

/-- Consecutive Fibonacci numbers F₄₂₀ and F₄₁₉. -/
def num : ℕ := 2662710205480735617346452022100755074809023407208374441801919604845563638678145849451440
def den : ℕ := 1645645409178311156114050175340179094658577397657624573049761120640548215334513341070281

theorem ceiling_mono {u v w z : ℕ} (hu : 0 < u) (hw : 0 < w) (comp : v*w ≤ z*u) (n : ℕ) :
    (v*n+u-1)/u ≤ (z*n+w-1)/w := by
  rw [← Nat.ceilDiv_eq_add_pred_div,← Nat.ceilDiv_eq_add_pred_div]
  apply (ceilDiv_le_iff_le_mul hu).mpr
  have hz : z*n ≤ w*(z*n ⌈/⌉ w) := (ceilDiv_le_iff_le_mul hw).mp le_rfl
  apply Nat.le_of_mul_le_mul_left _ hw
  calc w*(v*n) = v*w*n := by ring
       _ ≤ z*u*n := Nat.mul_le_mul_right n comp
       _ = u*(z*n) := by ring
       _ ≤ u*(w*(z*n ⌈/⌉ w)) := Nat.mul_le_mul_left u hz
       _ = w*(u*(z*n ⌈/⌉ w)) := by ring

theorem all_lengths (n : ℕ) : (D+2)*rothNumberNat n ≤ D*rothNumberNat ((num*n+den-1)/den) := by
  have hd : 0 < den := by decide +kernel
  by_cases high : seedThreshold ≤ n
  · have comp : B*den ≤ num*A := by decide +kernel
    have order := ceiling_mono (by decide +kernel : 0<A) hd comp n
    exact (Erdos142ExactRoth.ceil_growth n high).trans (Nat.mul_le_mul_left D (rothNumberNat.monotone order))
  obtain rfl | lo := n.eq_zero_or_pos
  · simp
  have hs : n ≤ Erdos142ShortPrefix.T := by
    have eq : seedThreshold=Erdos142ShortPrefix.T := by decide +kernel
    omega
  have hg := Erdos142ShortPrefix.strict_growth n lo hs
  have comp : Erdos142ShortPrefix.V*den ≤ num*Erdos142ShortPrefix.U := by decide +kernel
  have order := ceiling_mono (by decide +kernel : 0<Erdos142ShortPrefix.U) hd comp n
  have strict := hg.trans_le (rothNumberNat.monotone order)
  have small : 2*rothNumberNat n ≤ D := by
    have h₁ := rothNumberNat_le n
    have h₂ : 2*seedThreshold ≤ D := by decide +kernel
    omega
  have bound := Nat.mul_le_mul_left D (show rothNumberNat n+1 ≤ _ from strict)
  nlinarith only [bound,small]

theorem below_golden : (num:ℝ) < (den:ℝ)*Real.goldenRatio := by
  have hnat : num^2 < num*den+den^2 := by decide +kernel
  have h : (num:ℝ)^2 < (num:ℝ)*den+(den:ℝ)^2 := by exact_mod_cast hnat
  by_contra! ge
  have pos := mul_nonneg (Nat.cast_nonneg den : (0:ℝ) ≤ den) (sub_nonneg.mpr Real.one_lt_goldenRatio.le)
  have right : 0 ≤ (num:ℝ)+(den:ℝ)*Real.goldenRatio-den := by linarith [Nat.cast_nonneg (α:=ℝ) num]
  have w := mul_nonneg (sub_nonneg.mpr ge) right
  have eq := congrArg (fun z : ℝ => z*(den:ℝ)^2) Real.goldenRatio_sq
  nlinarith only [w,eq,h]

theorem golden_ceiling (n : ℕ) :
    (D+2)*rothNumberNat n ≤ D*rothNumberNat ⌈Real.goldenRatio*n⌉₊ := by
  apply (all_lengths n).trans
  apply Nat.mul_le_mul_left D
  apply rothNumberNat.monotone
  rw [← Nat.ceilDiv_eq_add_pred_div]
  apply (ceilDiv_le_iff_le_mul (by decide +kernel : 0 < den)).mpr
  have h : (num:ℝ)*(n:ℝ) ≤ (den:ℝ)*((⌈Real.goldenRatio*n⌉₊:ℕ):ℝ) := by
    calc (num:ℝ)*n ≤ ((den:ℝ)*Real.goldenRatio)*n := mul_le_mul_of_nonneg_right below_golden.le (Nat.cast_nonneg _)
         _ = (den:ℝ)*(Real.goldenRatio*n) := mul_assoc _ _ _
         _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg _)
  exact_mod_cast h

theorem fibonacci_ratio : num = Nat.fib 420 ∧ den = Nat.fib 419 := by
  simp only [Nat.fib_eq_fastFib]
  decide +kernel

/-- At least one additional point fits, even at the smallest positive lengths. -/
theorem strict_golden (n : ℕ) (hn : 0 < n) : rothNumberNat n < rothNumberNat ⌈Real.goldenRatio*n⌉₊ := by
  by_contra! le
  have h := (golden_ceiling n).trans (Nat.mul_le_mul_left D le)
  have pos := Erdos142ShortPrefix.roth_positive hn
  nlinarith only [h,pos]

#print axioms strict_golden
#print axioms all_lengths
#print axioms below_golden
#print axioms golden_ceiling
end Erdos142AllLengths
