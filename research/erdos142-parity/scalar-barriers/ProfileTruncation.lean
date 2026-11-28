import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Truncating a scalar Roth profile to its lower linear envelope.
The tail begins at T. When G(T)=βT the two definitions agree there. -/

namespace Erdos142Truncation

noncomputable def cut (G : ℝ → ℝ) (β T x : ℝ) : ℝ :=
  if x < T then G x else β*x

theorem left {G : ℝ → ℝ} {β T x : ℝ} (matchT : G T = β*T) (h : x ≤ T) :
    cut G β T x = G x := by
  rcases h.eq_or_lt with rfl|lt
  · simp [cut, matchT]
  · simp [cut, lt]

theorem right {G : ℝ → ℝ} {β T x : ℝ} (h : T ≤ x) :
    cut G β T x = β*x := by simp [cut, not_lt.mpr h]

theorem monotone {G : ℝ → ℝ} {β T : ℝ} (original : Monotone G)
    (b : 0 ≤ β) (matchT : G T = β*T) : Monotone (cut G β T) := by
  intro x y xy
  by_cases h : y < T
  · rw [left matchT (xy.trans h.le),left matchT h.le]
    exact original xy
  · rw [right (le_of_not_gt h)]
    by_cases a : x < T
    · rw [left matchT a.le]
      exact (original a.le).trans (matchT ▸ mul_le_mul_of_nonneg_left (le_of_not_gt h) b)
    · rw [right (le_of_not_gt a)]
      exact mul_le_mul_of_nonneg_left xy b

theorem envelopes {G : ℝ → ℝ} {β T x : ℝ} (lo : β*x ≤ G x) :
    β*x ≤ cut G β T x ∧ cut G β T x ≤ G x := by
  by_cases h : x < T <;> simp [cut,h,lo]

theorem subadditive {G : ℝ → ℝ} {β T : ℝ}
    (lower : ∀ t ≥ 0, β*t ≤ G t)
    (original : ∀ u ≥ 0, ∀ v ≥ 0, G (u+v) ≤ G u + G v)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cut G β T (x+y) ≤ cut G β T x + cut G β T y := by
  by_cases h : x+y < T
  · simp only [cut,if_pos h,if_pos (show x<T by linarith),if_pos (show y<T by linarith)]
    exact original x hx y hy
  · rw [right (le_of_not_gt h),mul_add]
    exact add_le_add (envelopes (T := T) (lower x hx)).1 (envelopes (T := T) (lower y hy)).1

/-- For z=x+2y past the cutoff, βy≥2M absorbs both possible errors M. -/
theorem glue {G : ℝ → ℝ} {β M T : ℝ} (b : 0 ≤ β)
    (lower : ∀ t ≥ 0, β*t ≤ G t) (upper : ∀ t ≥ 0, G t ≤ β*t+M)
    (original : ∀ u ≥ 0, ∀ v ≥ u, G u + G v ≤ G (u+2*v))
    (cutoff : 6*M ≤ β*T) {x y : ℝ} (hx : 0 ≤ x) (xy : x ≤ y) :
    cut G β T x + cut G β T y ≤ cut G β T (x+2*y) := by
  have hy := hx.trans xy
  have ex := (envelopes (T := T) (lower x hx)).2
  have ey := (envelopes (T := T) (lower y hy)).2
  by_cases h : x+2*y < T
  · simpa only [cut,if_pos h] using (add_le_add ex ey).trans (original x hx y xy)
  · rw [right (le_of_not_gt h)]
    have slope := mul_le_mul_of_nonneg_left (show T ≤ 3*y by linarith) b
    nlinarith [upper x hx,upper y hy]

/-- A small multiplier uses 2ML≤βT and 3r≤2L. A large multiplier is
covered directly by r≤βL. L=r=1 is the identity. -/
theorem digit {G : ℝ → ℝ} {β M T L r : ℝ} (b : 0 ≤ β) (lp : 0 < L)
    (rp : 0 ≤ r) (lower : ∀ t ≥ 0, β*t ≤ G t)
    (upper : ∀ t ≥ 0, G t ≤ β*t+M) (upperId : ∀ t ≥ 0, G t ≤ t)
    (original : ∀ t ≥ 0, r*G t ≤ G (L*t))
    (cases : (r=1 ∧ L=1) ∨ r ≤ β*L ∨ (3*r ≤ 2*L ∧ 2*M*L ≤ β*T))
    {x : ℝ} (hx : 0 ≤ x) : r * cut G β T x ≤ cut G β T (L*x) := by
  rcases cases with ⟨rfl,rfl⟩|hm
  · simp
  have ex := (envelopes (T := T) (lower x hx)).2
  by_cases h : L*x < T
  · simp only [cut,if_pos h] at *
    exact (mul_le_mul_of_nonneg_left ex rp).trans (original x hx)
  rw [right (le_of_not_gt h)]
  rcases hm with big|⟨count,small⟩
  · have bound := mul_le_mul_of_nonneg_left (ex.trans (upperId x hx)) rp
    nlinarith [mul_le_mul_of_nonneg_right big hx]
  · have slope := mul_le_mul_of_nonneg_left (le_of_not_gt h) b
    have enough : 2*M ≤ β*x := by
      exact (mul_le_mul_iff_left₀ lp).mp (show 2*M*L ≤ (β*x)*L by nlinarith)
    have bound := mul_le_mul_of_nonneg_left (ex.trans (upper x hx)) rp
    nlinarith [mul_le_mul_of_nonneg_left enough rp,
      mul_le_mul_of_nonneg_right count (mul_nonneg b hx)]

/-- Application to a single cutoff T=620W with Wβ=M. For large m the only
remaining input is the previously checked linear upper bound for Roth numbers. -/
theorem roth_digits {G : ℝ → ℝ} {β W M : ℝ} (b : 0 ≤ β) (mass : 0 ≤ M)
    (scale : β*W=M) (lower : ∀ t ≥ 0, β*t ≤ G t)
    (upper : ∀ t ≥ 0, G t ≤ β*t+M) (upperId : ∀ t ≥ 0, G t ≤ t)
    (original : ∀ m : ℕ, 0 < m → ∀ t ≥ 0, (rothNumberNat m : ℝ)*G t ≤ G ((2*(m:ℝ)-1)*t))
    (large : ∀ m : ℕ, 155 ≤ m → (rothNumberNat m : ℝ) ≤ β*(2*(m:ℝ)-1))
    {m : ℕ} (hm : 0 < m) {x : ℝ} (hx : 0 ≤ x) :
    (rothNumberNat m : ℝ)*cut G β (620*W) x ≤ cut G β (620*W) ((2*(m:ℝ)-1)*x) := by
  have mh : (1:ℝ) ≤ m := by exact_mod_cast hm
  have rh : (rothNumberNat m : ℝ) ≤ m := by exact_mod_cast rothNumberNat_le m
  apply digit b (by linarith) (Nat.cast_nonneg _) lower upper upperId (original m hm) _ hx
  by_cases one : m=1
  · subst m
    by_cases eq : rothNumberNat 1=1
    · exact Or.inl ⟨by exact_mod_cast eq, by norm_num⟩
    · have h : rothNumberNat 1=0 := by have := rothNumberNat_le 1; omega
      exact Or.inr (Or.inl (by rw [h];norm_num;exact b))
  by_cases big : 155 ≤ m
  · exact Or.inr (Or.inl (large m big))
  · have mlo : (2:ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
    have mhi : (m:ℝ) ≤ 154 := by exact_mod_cast (show m ≤ 154 by omega)
    exact Or.inr (Or.inr ⟨by linarith,by
      nlinarith [mul_le_mul_of_nonneg_right mhi mass]⟩)

#print axioms subadditive
#print axioms glue
#print axioms digit
#print axioms roth_digits
end Erdos142Truncation
