import DoublingGrowth
import RothHeight
import Mathlib.Combinatorics.Additive.AP.Three.Behrend

/-! Numerical seed, scaling, and rounding from integer grids to every large length. -/
namespace Erdos142SubgoldenRoth

abbrev W : ℕ := 511^14
abbrev C : ℕ := 2^92+1

theorem seed : C ≤ rothNumberNat W := by
  have h := Behrend.bound_aux (d := 256) (n := 14) (by decide) (by decide)
  have e : ((2^92+1 : ℕ) : ℝ) ≤ (256 : ℝ)^(14-2 : ℕ)/14 := by norm_num
  exact_mod_cast e.trans h

theorem unbounded (h : ℕ) : ∃ N, ∀ n ≥ N, h ≤ rothNumberNat n := by
  let d := 3*h+1
  refine ⟨(2*d-1)^3, fun n hn => ?_⟩
  have hb := Behrend.bound_aux (d := d) (n := 3) (by dsimp [d]; omega) (by decide)
  have hc : (h : ℝ) ≤ (d : ℝ)^(3-2 : ℕ)/3 := by simp [d]; linarith
  exact le_trans (by exact_mod_cast hc.trans hb) (rothNumberNat.monotone hn)

def profile (t j : ℕ) : ℤ := rothNumberNat (j*t)

theorem mono (t : ℕ) : Monotone (profile t) := by
  intro x y h
  dsimp [profile]
  exact_mod_cast rothNumberNat.monotone (Nat.mul_le_mul_right t h)

theorem sub (t x y : ℕ) : profile t (x+y) ≤ profile t x + profile t y := by
  dsimp [profile]; rw [Nat.add_mul]
  exact_mod_cast rothNumberNat_add_le (x*t) (y*t)

theorem glue (t x y : ℕ) (hy : y ≤ x) : profile t x + profile t y ≤ profile t (2*x+y) := by
  have h := Erdos142DoublingGrowth.interp_glue 1 (x*t) (y*t) (by decide) (Nat.mul_le_mul_right t hy)
  simp only [Erdos142GridInterpolation.interp, Nat.mod_one, Nat.sub_zero, Nat.div_one,
    Nat.one_mul, Nat.zero_mul, Nat.add_zero] at h
  dsimp [profile]; rw [Nat.add_mul, Nat.mul_assoc]; exact_mod_cast h

theorem digit {a b : ℕ} (h : 2*W*a ≤ b) (t : ℕ) : (C : ℤ)*profile t a ≤ profile t b := by
  have hh := Erdos142Height.digit_product W (a*t)
  have hfinal := (Nat.mul_le_mul_right (rothNumberNat (a*t)) seed).trans hh
  have hfit : 2*W*(a*t) ≤ b*t := by rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right t h
  dsimp [profile]
  exact_mod_cast hfinal.trans (rothNumberNat.monotone hfit)

/-- Any strict multiplicative improvement on multiples yields a uniform eventual
improvement at the same rational dilation. -/
theorem round_grid {a b d : ℕ} (ha : 0 < a)
    (grid : ∀ t : ℕ, (d+1)*rothNumberNat (a*t) ≤ d*rothNumberNat (b*t)) :
    ∃ N, ∀ n ≥ N, (2*d+1)*rothNumberNat n ≤ 2*d*rothNumberNat (b*n/a) := by
  obtain ⟨N,hN⟩ := unbounded (2*(d+1)*a)
  refine ⟨N, fun n hn => ?_⟩
  let t := n / a
  have hlo : a*t ≤ n := Nat.mul_div_le n a
  have rem : n % a ≤ a := (Nat.mod_lt n ha).le
  have up : rothNumberNat n ≤ rothNumberNat (a*t)+a := by
    calc rothNumberNat n = rothNumberNat (a*t+n%a) := congrArg _ (Nat.div_add_mod n a).symm
         _ ≤ _ := rothNumberNat_add_le _ _
         _ ≤ _ := Nat.add_le_add_left ((rothNumberNat_le _).trans rem) _
  have fit : b*t ≤ b*n/a := by
    apply (Nat.le_div_iff_mul_le ha).mpr
    calc b*t*a = b*(a*t) := by ring
         _ ≤ b*n := Nat.mul_le_mul_left b hlo
  have hgrid := (grid t).trans (Nat.mul_le_mul_left d (rothNumberNat.monotone fit))
  have hscaled := Nat.mul_le_mul_left (2*(d+1)) up
  have large := hN n hn
  nlinarith only [hgrid, hscaled, large]

#print axioms seed
#print axioms round_grid
end Erdos142SubgoldenRoth
