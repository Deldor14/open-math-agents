import ExactGrid
import ExactInterpolation
import ChargedGeometry
import Mathlib.Combinatorics.Additive.AP.Three.Behrend

/-! Explicit lower growth at every sufficiently large integer below the golden ratio. -/
namespace Erdos142ExactRoth
open Erdos142ExactGrid

private theorem a_pos : 0 < A := by decide +kernel

private theorem seed (n : ℕ) : C*rothNumberNat n ≤ rothNumberNat (M*n) := by
  rw [show M=59^3*61^9 by decide +kernel, show C=2303115151489024 by rfl]
  simpa only [Erdos142Charged.sphere_card] using Erdos142Charged.charged_product n

private theorem fit (n : ℕ) (hn : seedThreshold ≤ n) : M*(a₀*n+A) ≤ B*n := by
  have h₁ : M*A ≤ (B-M*a₀)*seedThreshold := by decide +kernel
  have h₂ : M*a₀ ≤ B := by decide +kernel
  have h := h₁.trans (Nat.mul_le_mul_left (B-M*a₀) hn)
  have hsum : B-M*a₀+M*a₀ = B := Nat.sub_add_cancel h₂
  calc M*(a₀*n+A) = M*A+(M*a₀)*n := by ring
       _ ≤ (B-M*a₀)*n+(M*a₀)*n := Nat.add_le_add_right h _
       _ = B*n := by rw [← Nat.add_mul,hsum]

private theorem interp_growth (n : ℕ) (hn : seedThreshold ≤ n) :
    ((D:ℤ)+2)*((A:ℤ)*rothNumberNat n) ≤ (D:ℤ)*Erdos142ExactInterp.P A n B := by
  have hs := Erdos142ExactInterp.digit A n a₀ B C M a_pos seed (fit n hn)
  have h := Erdos142ExactGrid.abstract (Erdos142ExactInterp.P A n) (Erdos142ExactInterp.mono A n a_pos) (Erdos142ExactInterp.sub A n a_pos) (Erdos142ExactInterp.glue A n a_pos) hs
  rw [Erdos142ExactInterp.at_den A n a_pos] at h
  linarith only [h]

/-- Rounding up delivers the full gain at a lower input threshold. -/
theorem ceil_growth (n : ℕ) (hn : seedThreshold ≤ n) :
    (D+2)*rothNumberNat n ≤ D*rothNumberNat ((B*n+A-1)/A) := by
  have h := (interp_growth n hn).trans (mul_le_mul_of_nonneg_left (Erdos142ExactInterp.upper_ceil A n B a_pos) (Int.natCast_nonneg D))
  have w : ((D:ℤ)+2)*(rothNumberNat n:ℤ) ≤ (D:ℤ)*(rothNumberNat ((B*n+A-1)/A):ℤ) := by
    apply le_of_mul_le_mul_left (a:=(A:ℤ)) _ (by exact_mod_cast a_pos)
    nlinarith only [h]
  exact_mod_cast w

/-- Increasing the numerator by one retains a subgolden dilation and avoids any loss on rounding. -/
theorem nearby_floor_growth (n : ℕ) (hn : A ≤ n) :
    (D+2)*rothNumberNat n ≤ D*rothNumberNat ((B+1)*n/A) := by
  have hs : seedThreshold ≤ A := by decide +kernel
  have h := (interp_growth n (hs.trans hn)).trans (mul_le_mul_of_nonneg_left (Erdos142ExactInterp.upper_next A n B a_pos hn) (Int.natCast_nonneg D))
  have w : ((D:ℤ)+2)*(rothNumberNat n:ℤ) ≤ (D:ℤ)*(rothNumberNat ((B+1)*n/A):ℤ) := by
    apply le_of_mul_le_mul_left (a:=(A:ℤ)) _ (by exact_mod_cast a_pos)
    nlinarith only [h]
  exact_mod_cast w

/-- A separate Behrend sphere pays the one-site error at the original dilation. -/
theorem floor_growth (n : ℕ) (hn : 94003^31 ≤ n) :
    (D+1)*rothNumberNat n ≤ D*rothNumberNat (B*n/A) := by
  have hs : seedThreshold ≤ 94003^31 := by decide +kernel
  have h := (interp_growth n (hs.trans hn)).trans (mul_le_mul_of_nonneg_left (Erdos142ExactInterp.upper_floor_add_one A n B a_pos) (Int.natCast_nonneg D))
  have large : D ≤ rothNumberNat n := by
    have hB := Behrend.bound_aux (d:=47002) (n:=31) (by decide) (by decide)
    have hD : (D:ℝ) ≤ (47002:ℝ)^(31-2:ℕ)/31 := by norm_num [D]
    have hsph : D ≤ rothNumberNat ((2*47002-1)^31) := by exact_mod_cast hD.trans hB
    exact hsph.trans (rothNumberNat.monotone hn)
  have pre : ((D:ℤ)+2)*(rothNumberNat n:ℤ) ≤ (D:ℤ)*((rothNumberNat (B*n/A):ℤ)+1) := by
    apply le_of_mul_le_mul_left (a:=(A:ℤ)) _ (by exact_mod_cast a_pos)
    nlinarith only [h]
  have w : ((D:ℤ)+1)*(rothNumberNat n:ℤ) ≤ (D:ℤ)*(rothNumberNat (B*n/A):ℤ) := by
    have e : (D:ℤ) ≤ (rothNumberNat n:ℤ) := by exact_mod_cast large
    nlinarith only [pre,e]
  exact_mod_cast w

#print axioms ceil_growth
#print axioms nearby_floor_growth
#print axioms floor_growth
end Erdos142ExactRoth
