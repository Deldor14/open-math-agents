import RothHeight
import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! The logarithmic dyadic Roth deficit and its discrete generalized inverse.
The underlying digit-product inequality is the one in Erdos142Height.
Natural logarithms are used throughout. -/

namespace Erdos142Deficit
open Real Filter Asymptotics

private def count (t : ℕ) : ℝ := rothNumberNat (2^t)

private theorem count_pos (t : ℕ) : 0 < count t := by
  have free : ThreeAPFree (({0}:Finset ℕ):Set ℕ) := by simp
  have h : 1 ≤ rothNumberNat (2^t) := free.le_rothNumberNat _ (by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    positivity) (by simp)
  dsimp [count]
  exact_mod_cast (show 0 < rothNumberNat (2^t) by omega)

private theorem count_double (t : ℕ) : count (t+1) ≤ 2*count t := by
  have sub := rothNumberNat_add_le (2^t) (2^t)
  rw [show 2^t+2^t=(2:ℕ)^(t+1) by rw [pow_succ];omega] at sub
  dsimp [count]
  exact_mod_cast (show rothNumberNat (2^(t+1)) ≤ 2*rothNumberNat (2^t) by omega)

private theorem count_mono (t : ℕ) : count t ≤ count (t+1) := by
  dsimp [count]
  exact_mod_cast rothNumberNat.monotone (show 2^t ≤ (2:ℕ)^(t+1) by rw [pow_succ];omega)

noncomputable def deficit (t : ℕ) : ℝ := Real.log ((2:ℝ)^t/count t)
noncomputable def e (t : ℕ) : ℝ := deficit t+Real.log 2

theorem deficit_formula (t : ℕ) :
    deficit t = (t:ℝ)*Real.log 2 - Real.log (rothNumberNat (2^t):ℝ) := by
  rw [deficit,Real.log_div (by positivity) (count_pos t).ne',Real.log_pow]
  rfl

theorem deficit_mono : Monotone deficit := by
  apply monotone_nat_of_le_succ
  intro t
  have h := Real.log_le_log (count_pos (t+1)) (count_double t)
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (count_pos t).ne'] at h
  simp only [deficit_formula,Nat.cast_add,Nat.cast_one]
  unfold count at h
  linarith

theorem deficit_step (t : ℕ) : deficit (t+1)-deficit t ≤ Real.log 2 := by
  have h := Real.log_le_log (count_pos t) (count_mono t)
  simp only [deficit_formula,Nat.cast_add,Nat.cast_one]
  unfold count at h
  linarith

theorem e_zero : e 0=Real.log 2 := by
  have pos : 0 < rothNumberNat 1 := by
    have h := count_pos 0
    simp only [count,pow_zero] at h
    exact_mod_cast h
  have one : rothNumberNat 1=1 := by have h := rothNumberNat_le 1;omega
  simp [e,deficit_formula,one]

theorem e_mono : Monotone e := by
  intro s t h
  unfold e
  linarith only [deficit_mono h]

theorem e_step (t : ℕ) : e (t+1)-e t ≤ Real.log 2 := by
  unfold e
  linarith only [deficit_step t]

theorem e_subadd (s t : ℕ) : e (s+t) ≤ e s + e t := by
  have shift : 2*(2:ℕ)^s*2^t=2^(s+t+1) := by rw [pow_succ,pow_add];ring
  have product := Erdos142Height.digit_product (2^s) (2^t)
  rw [shift] at product
  have real_product : count s*count t ≤ count (s+t+1) := by unfold count; exact_mod_cast product
  have h := Real.log_le_log (mul_pos (count_pos s) (count_pos t))
    (real_product.trans (count_double (s+t)))
  rw [Real.log_mul (count_pos s).ne' (count_pos t).ne',
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (count_pos _).ne'] at h
  unfold count at h
  simp only [e,deficit_formula,Nat.cast_add]
  linarith

/-- Roth's density-zero theorem makes the adjusted deficit unbounded. -/
theorem e_unbounded (y : ℝ) : ∃ t, y < e t := by
  have pos := Real.exp_pos (y+1)
  have h := (isLittleO_iff.mp rothNumberNat_isLittleO_id)
    (show 0 < (Real.exp (y+1))⁻¹ by positivity)
  simp only [RCLike.norm_natCast] at h
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  have hn : count N ≤ (Real.exp (y+1))⁻¹*(2:ℝ)^N := by
    simpa [count] using hN (2^N) (Nat.lt_two_pow_self.le)
  have hmul := mul_le_mul_of_nonneg_left hn pos.le
  have paid : Real.exp (y+1)*count N ≤ (2:ℝ)^N := by
    simpa [← mul_assoc, pos.ne'] using hmul
  have logbound : y+1 ≤ deficit N := (Real.le_log_iff_exp_le
    (div_pos (by positivity) (count_pos N))).mpr ((le_div_iff₀ (count_pos N)).mpr paid)
  refine ⟨N,?_⟩
  unfold e
  linarith [Real.log_pos (by norm_num : (1:ℝ)<2)]

section GeneralInverse
variable (f : ℕ → ℝ) (unbounded : ∀ y : ℝ, ∃ t, y < f t)

/-- The last integer whose value is at most y, when y ≥ f(0). -/
noncomputable def T (y : ℝ) : ℕ := by
  classical
  exact Nat.find (unbounded y)-1

theorem inverse_bounds {y : ℝ} (hy : f 0 ≤ y) :
    f (T f unbounded y) ≤ y ∧ y < f (T f unbounded y+1) := by
  classical
  let k := Nat.find (unbounded y)
  have high : y < f k := Nat.find_spec (unbounded y)
  have pos : 0 < k := by
    by_contra! bad
    rw [show k=0 by omega] at high
    linarith
  change f (k-1) ≤ y ∧ y < f (k-1+1)
  rw [Nat.sub_one_add_one_eq_of_pos pos]
  exact ⟨le_of_not_gt (Nat.find_min (unbounded y) (show k-1<k by omega)),high⟩

theorem inverse_max (mono : Monotone f) {t : ℕ} {y : ℝ} (ht : f t ≤ y) :
    t ≤ T f unbounded y := by
  by_contra! bad
  have hy := (mono (Nat.zero_le t)).trans ht
  have high := (inverse_bounds f unbounded hy).2
  have le := mono (show T f unbounded y+1 ≤ t by omega)
  linarith

theorem inverse_superadditive (mono : Monotone f) (sub : ∀ i j, f (i+j) ≤ f i+f j)
    {y z : ℝ} (hy : f 0 ≤ y) (hz : f 0 ≤ z) :
    T f unbounded y + T f unbounded z ≤ T f unbounded (y+z) := by
  apply inverse_max f unbounded mono
  exact (sub _ _).trans (add_le_add (inverse_bounds f unbounded hy).1
    (inverse_bounds f unbounded hz).1)

theorem inverse_error {b y : ℝ} (step : ∀ t, f (t+1)-f t ≤ b) (hy : f 0 ≤ y) :
    y-b < f (T f unbounded y) ∧ f (T f unbounded y) ≤ y := by
  obtain ⟨low,high⟩ := inverse_bounds f unbounded hy
  exact ⟨by linarith only [high,step (T f unbounded y)],low⟩

end GeneralInverse

noncomputable abbrev last (y : ℝ) := T e e_unbounded y

theorem last_superadditive {y z : ℝ} (hy : e 0 ≤ y) (hz : e 0 ≤ z) :
    last y + last z ≤ last (y+z) := inverse_superadditive e e_unbounded e_mono e_subadd hy hz

theorem last_error {y : ℝ} (hy : e 0 ≤ y) :
    y-Real.log 2 < e (last y) ∧ e (last y) ≤ y := inverse_error e e_unbounded e_step hy

#print axioms deficit_mono
#print axioms e_subadd
#print axioms e_unbounded
#print axioms last_superadditive
#print axioms last_error
end Erdos142Deficit
