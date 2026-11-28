import Mathlib.Tactic

namespace SepticOutputSupport

theorem growth (p v : ℕ) (hp : 17 ≤ p) (hv : 29 ≤ v) :
    7*(4*p)^6 < v^(p-6) := by
  have grow (k : ℕ) : 7*(4*(17+k))^6 < 29^(11+k) := by
    induction k with
    | zero => decide
    | succ k ih =>
      have b : 2*((17+k)+1) ≤ 3*(17+k) := by omega
      have powb := Nat.pow_le_pow_left b 6
      norm_num [mul_pow] at powb
      rw [show 11+k.succ=(11+k)+1 by omega, pow_succ]
      change 7*(4*((17+k)+1))^6 < _
      norm_num [mul_pow] at ih ⊢
      omega
  have bound := grow (p-17)
  rw [show 17+(p-17)=p by omega, show 11+(p-17)=p-6 by omega] at bound
  exact bound.trans_le (Nat.pow_le_pow_left hv (p-6))

theorem eleven_size {v : ℕ} (h : v^5 < 7*(4*11)^6) : v ≤ 138 := by
  by_contra! bad
  have h' := Nat.pow_le_pow_left bad 5
  norm_num at h h'
  omega

theorem thirteen_size {v : ℕ} (h : v^7 < 7*(4*13)^6) : v ≤ 39 := by
  by_contra! bad
  have h' := Nat.pow_le_pow_left bad 7
  norm_num at h h'
  omega

/-- All six surviving pairs fail at the same prime of good reduction. -/
theorem finite_residues (a : ZMod 83) :
    (a+1)^7-a^7 ≠ (29 : ZMod 83)^11 ∧
    (a+1)^7-a^7 ≠ (43 : ZMod 83)^11 ∧
    (a+1)^7-a^7 ≠ (71 : ZMod 83)^11 ∧
    (a+1)^7-a^7 ≠ (113 : ZMod 83)^11 ∧
    (a+1)^7-a^7 ≠ (127 : ZMod 83)^11 ∧
    (a+1)^7-a^7 ≠ (29 : ZMod 83)^13 := by
  revert a
  set_option maxRecDepth 8192 in
  set_option maxHeartbeats 2000000 in
  decide

end SepticOutputSupport
