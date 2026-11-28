import DoublingGrowth

/-! Deldor14. Growth at the rational dilation 5/3 and the local step
in the quantitative Fibonacci argument. For interpolation, see eilamc14's
DoublingGrowth.lean at d8ca5d4abbf28eb0af283e37f6b4c5f3162bf5ae. -/

namespace Erdos142ScaleSteps
open Erdos142GridInterpolation Erdos142DoublingGrowth

set_option maxHeartbeats 3000000 in
theorem certificate (F : ℕ → ℤ)
    (sub : ∀ a b, F (a+b) ≤ F a + F b)
    (glue : ∀ a b, b ≤ a → F a + F b ≤ F (2*a+b)) :
    128 * F 144 ≤ 127 * F 240 := by
  linear_combination
    2 * (glue 11 11 (by decide)) +
    2 * (glue 12 12 (by decide)) +
    4 * (glue 31 30 (by decide)) +
    2 * (glue 33 28 (by decide)) +
    2 * (glue 36 22 (by decide)) +
    4 * (glue 37 20 (by decide)) +
    4 * (glue 38 19 (by decide)) +
    34 * (sub 80 64) +
    17 * (glue 80 80 (by decide)) +
    34 * (sub 88 56) +
    34 * (glue 88 64 (by decide)) +
    30 * (sub 92 52) +
    34 * (glue 92 56 (by decide)) +
    4 * (sub 94 20) +
    2 * (sub 94 28) +
    4 * (sub 94 31) +
    12 * (sub 94 50) +
    30 * (glue 94 52 (by decide)) +
    4 * (sub 95 12) +
    4 * (sub 95 38) +
    12 * (glue 95 50 (by decide)) +
    4 * (sub 107 37) +
    4 * (sub 114 30) +
    2 * (sub 122 22) +
    4 * (sub 125 19) +
    4 * (sub 133 11)

theorem five_thirds (n : ℕ) :
    128 * rothNumberNat (3*n) ≤ 127 * rothNumberNat (5*n) := by
  let F := fun i : ℕ => (interp 48 (i*n) : ℤ)
  have S (a b : ℕ) : F (a+b) ≤ F a + F b := by
    dsimp [F]
    rw [Nat.add_mul]
    exact_mod_cast interp_subadd 48 (a*n) (b*n) (by decide)
  have G (a b : ℕ) (h : b ≤ a) : F a + F b ≤ F (2*a+b) := by
    dsimp [F]
    rw [Nat.add_mul, Nat.mul_assoc]
    exact_mod_cast interp_glue 48 (a*n) (b*n) (by decide) (Nat.mul_le_mul_right n h)
  have h := certificate F S G
  have exactGrid (k : ℕ) : interp 48 (48*k) = 48 * rothNumberNat k := by
    simp only [interp, Nat.mul_mod_right, Nat.sub_zero,
      Nat.mul_div_cancel_left k (by decide : 0 < 48), Nat.zero_mul, Nat.add_zero]
  change 128 * (interp 48 (144*n) : ℤ) ≤ 127 * (interp 48 (240*n) : ℤ) at h
  rw [show 144*n=48*(3*n) by omega, show 240*n=48*(5*n) by omega, exactGrid, exactGrid] at h
  push_cast at h
  omega

theorem one_step (F : ℕ → ℤ) (mono : Monotone F)
    (sub : ∀ a b, F (a+b) ≤ F a + F b)
    (glue : ∀ a b, b ≤ a → F a + F b ≤ F (2*a+b))
    (A B x y : ℕ) (hx : x ≤ A)
    (fit : y + (A-x) + max y (A-x) ≤ B) :
    F y - F x ≤ F B - F A := by
  have h := sub x (A-x)
  rw [show x+(A-x)=A by omega] at h
  rcases le_total (A-x) y with h₁ | h₂
  · rw [max_eq_left h₁] at fit
    have g := (glue y (A-x) h₁).trans (mono (show 2*y+(A-x) ≤ B by omega))
    omega
  · rw [max_eq_right h₂] at fit
    have g := (glue (A-x) y h₂).trans (mono (show 2*(A-x)+y ≤ B by omega))
    omega

#print axioms five_thirds
#print axioms one_step
end Erdos142ScaleSteps
