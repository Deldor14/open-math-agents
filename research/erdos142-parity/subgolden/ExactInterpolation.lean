import DoublingGrowth

/-! Exact interpolation and rounding for the mixed-radix Roth growth
estimate in note #172398. The straight-line numerator, subadditivity,
and gluing on rational grids are due to eilamc14 (DoublingGrowth.lean). -/

namespace Erdos142ExactInterp
open Erdos142GridInterpolation Erdos142DoublingGrowth

def P (A n j : ℕ) : ℤ := interp A (j*n)

theorem mono (A n : ℕ) (hA : 0 < A) : Monotone (P A n) := by
  intro x y xy
  unfold P
  exact_mod_cast interp_mono A hA (Nat.mul_le_mul_right n xy)

theorem sub (A n : ℕ) (hA : 0 < A) (x y : ℕ) : P A n (x+y) ≤ P A n x+P A n y := by
  unfold P
  rw [Nat.add_mul]
  exact_mod_cast interp_subadd A (x*n) (y*n) hA

theorem glue (A n : ℕ) (hA : 0 < A) (x y : ℕ) (hy : y ≤ x) :
    P A n x+P A n y ≤ P A n (2*x+y) := by
  unfold P
  rw [Nat.add_mul,Nat.mul_assoc]
  exact_mod_cast interp_glue A (x*n) (y*n) hA (Nat.mul_le_mul_right n hy)

private theorem integral (A k : ℕ) (hA : 0 < A) : interp A (A*k) = A*rothNumberNat k := by
  simp [interp,Nat.mul_div_cancel_left k hA]

theorem at_den (A n : ℕ) (hA : 0 < A) : P A n A = (A:ℤ)*rothNumberNat n := by
  unfold P
  exact_mod_cast integral A n hA

private theorem lower {A x k : ℕ} (hA : 0 < A) (fit : A*k ≤ x) :
    A*rothNumberNat k ≤ interp A x := (integral A k hA).symm.le.trans ((interp_mono A hA) fit)

private theorem upper {A x k : ℕ} (hA : 0 < A) (fit : x ≤ A*k) :
    interp A x ≤ A*rothNumberNat k := ((interp_mono A hA) fit).trans (integral A k hA).le

private theorem floor_succ_cap {A x : ℕ} (hA : 0 < A) :
    x ≤ A*(x/A+1) := by
  rw [Nat.mul_succ]
  have recombine := Nat.div_add_mod x A
  have rem := Nat.mod_lt x hA
  omega

theorem upper_floor_add_one (A n B : ℕ) (hA : 0 < A) :
    P A n B ≤ (A:ℤ)*((rothNumberNat (B*n/A):ℤ)+1) := by
  have first := upper (x := B*n) hA (floor_succ_cap hA)
  have one : rothNumberNat (B*n/A+1) ≤ rothNumberNat (B*n/A)+1 :=
    (rothNumberNat_add_le _ 1).trans (Nat.add_le_add_left (rothNumberNat_le 1) _)
  unfold P
  exact_mod_cast first.trans (Nat.mul_le_mul_left A one)

theorem upper_ceil (A n B : ℕ) (hA : 0 < A) :
    P A n B ≤ (A:ℤ)*(rothNumberNat ((B*n+A-1)/A):ℤ) := by
  have fit : B*n ≤ A*((B*n+A-1)/A) := by
    rw [← Nat.ceilDiv_eq_add_pred_div]
    exact (ceilDiv_le_iff_le_mul hA).mp le_rfl
  unfold P
  exact_mod_cast upper hA fit

theorem upper_next (A n B : ℕ) (hA : 0 < A) (hn : A ≤ n) :
    P A n B ≤ (A:ℤ)*(rothNumberNat ((B+1)*n/A):ℤ) := by
  have inc : (B*n+A-1)/A ≤ (B+1)*n/A := by
    apply Nat.div_le_div_right
    rw [Nat.succ_mul]
    omega
  have h := (upper_ceil A n B hA)
  exact h.trans (by exact_mod_cast Nat.mul_le_mul_left A (rothNumberNat.monotone inc))

theorem digit (A n a B C M : ℕ) (hA : 0 < A)
    (seed : ∀ u : ℕ, C*rothNumberNat u ≤ rothNumberNat (M*u))
    (fit : M*(a*n+A) ≤ B*n) : (C:ℤ)*P A n a ≤ P A n B := by
  let u := a*n/A+1
  have above : a*n ≤ A*u := floor_succ_cap hA
  have below : A*u ≤ a*n+A := by
    dsimp [u]
    rw [Nat.mul_succ]
    exact Nat.add_le_add_right (Nat.mul_div_le _ _) _
  have reach : A*(M*u) ≤ B*n := by
    rw [Nat.mul_left_comm]
    exact (Nat.mul_le_mul_left M below).trans fit
  unfold P
  exact_mod_cast (calc
    C*interp A (a*n) ≤ C*(A*rothNumberNat u) := Nat.mul_le_mul_left C (upper hA above)
    _ = A*(C*rothNumberNat u) := Nat.mul_left_comm _ _ _
    _ ≤ A*rothNumberNat (M*u) := Nat.mul_le_mul_left A (seed u)
    _ ≤ interp A (B*n) := lower hA reach)

#print axioms mono
#print axioms sub
#print axioms glue
#print axioms at_den
#print axioms upper_floor_add_one
#print axioms upper_ceil
#print axioms upper_next
#print axioms digit
end Erdos142ExactInterp
