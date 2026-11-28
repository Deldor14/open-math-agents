import TunedNumeric
import ChargedInterpolation

/-! Growth for the actual interval Roth number at every input. The cyclic
interpolation inequality supplies the sphere multiplier on the entire mesh. -/

namespace Erdos142TunedRoth
open Erdos142TunedNumeric

private theorem a_pos : 0 < A := by decide +kernel

private theorem interp_growth (n : ℕ) :
    ((D:ℤ)+1)*((A:ℤ)*rothNumberNat n) ≤ (D:ℤ)*Erdos142ExactInterp.P A n B := by
  have hs := Erdos142Charged.charged_interpolation A n a₀ a_pos
  have seed : (C:ℤ)*Erdos142ExactInterp.P A n a₀ ≤ Erdos142ExactInterp.P A n (M*a₀) := by
    rw [show M = 59^3*61^9 by decide +kernel, show (C:ℤ) = 2303115151489024 by decide +kernel]
    exact hs
  have h := abstract_growth (Erdos142ExactInterp.P A n) (Erdos142ExactInterp.mono A n a_pos)
    (Erdos142ExactInterp.sub A n a_pos) (Erdos142ExactInterp.glue A n a_pos) seed
  rw [Erdos142ExactInterp.at_den A n a_pos] at h
  linarith only [h]

theorem ceil_growth (n : ℕ) :
    (D+1)*rothNumberNat n ≤ D*rothNumberNat ((B*n+A-1)/A) := by
  have h := (interp_growth n).trans (mul_le_mul_of_nonneg_left
    (Erdos142ExactInterp.upper_ceil A n B a_pos) (Int.natCast_nonneg D))
  have h' : ((D:ℤ)+1)*(rothNumberNat n:ℤ) ≤ (D:ℤ)*(rothNumberNat ((B*n+A-1)/A):ℤ) := by
    apply le_of_mul_le_mul_left (a:=(A:ℤ)) _ (by exact_mod_cast a_pos)
    nlinarith only [h]
  exact_mod_cast h'

theorem nearby_floor_growth (n : ℕ) (hn : A ≤ n) :
    (D+1)*rothNumberNat n ≤ D*rothNumberNat ((B+1)*n/A) := by
  have h := (interp_growth n).trans (mul_le_mul_of_nonneg_left
    (Erdos142ExactInterp.upper_next A n B a_pos hn) (Int.natCast_nonneg D))
  have h' : ((D:ℤ)+1)*(rothNumberNat n:ℤ) ≤ (D:ℤ)*(rothNumberNat ((B+1)*n/A):ℤ) := by
    apply le_of_mul_le_mul_left (a:=(A:ℤ)) _ (by exact_mod_cast a_pos)
    nlinarith only [h]
  exact_mod_cast h'

#print axioms ceil_growth
#print axioms nearby_floor_growth
end Erdos142TunedRoth
