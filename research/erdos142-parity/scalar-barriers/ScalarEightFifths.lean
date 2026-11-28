import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic

/-! An explicit nondecreasing profile with a plateau on [1,8/5]. The
inequalities for finite Roth numbers used here hold for all real inputs
of this scalar profile, including the digit products for every m ≥ 1. -/

namespace Erdos142Scalar

noncomputable section

private def shape (x : ℝ) : ℝ :=
  if x ≤ 2 then x else if x ≤ 3 then 2 else if x ≤ 5 then x-1
  else if x ≤ 8 then 4 else if x ≤ 15 then (4*x-4)/7
  else if x ≤ 16 then 8 else x/2

def profile (x : ℝ) : ℝ := shape (5*x)/4

private theorem shape_bounds {x : ℝ} (hx : 0 ≤ x) : x/2 ≤ shape x ∧ shape x ≤ x := by
  unfold shape
  split_ifs <;> constructor <;> linarith

set_option maxHeartbeats 8000000 in
private theorem shape_mono {x y : ℝ} (le : x ≤ y) : shape x ≤ shape y := by
  unfold shape
  split_ifs <;> linarith

set_option maxHeartbeats 100000000 in
private theorem shape_sub {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    shape (x+y) ≤ shape x + shape y := by
  unfold shape
  split_ifs <;> linarith

set_option maxHeartbeats 100000000 in
private theorem shape_glue {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    shape x + shape y ≤ shape (x+2*y) := by
  unfold shape
  split_ifs <;> linarith

theorem monotone : Monotone profile := by
  intro x y h
  exact div_le_div_of_nonneg_right (shape_mono (x := 5*x) (y := 5*y) (by linarith)) (by norm_num)

theorem linear_near_zero {x : ℝ} (hx : x ≤ 2/5) : profile x = 5*x/4 := by
  simp [profile,shape,show 5*x ≤ 2 by linarith]

theorem linear_at_infinity {x : ℝ} (hx : 16/5 ≤ x) : profile x = 5*x/8 := by
  unfold profile shape
  split_ifs <;> linarith

theorem plateau {x : ℝ} (lo : 1 ≤ x) (hi : x ≤ 8/5) : profile x = 1 := by
  unfold profile shape
  split_ifs <;> linarith

theorem interval_inequalities {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    profile (x+y) ≤ profile x + profile y ∧
    profile x + profile y ≤ profile (x+y+max x y) := by
  wlog hxy : x ≤ y generalizing x y
  · obtain ⟨s,g⟩ := this hy hx (by linarith : y ≤ x)
    simpa only [add_comm y x, max_comm y x, add_comm (profile y) (profile x)] using And.intro s g
  have pos : 0 ≤ 5*x := by linarith
  have ord : 5*x ≤ 5*y := by linarith
  have s := shape_sub pos ord
  have g := shape_glue pos ord
  unfold profile
  rw [max_eq_right hxy, show 5*(x+y)=5*x+5*y by linarith,
    show 5*(x+y+y)=5*x+2*(5*y) by linarith]
  constructor <;> linarith

private theorem roth_lt {m : ℕ} (hm : 3 ≤ m) : rothNumberNat m < m := by
  by_contra! h
  obtain ⟨T,incl,card,free⟩ := rothNumberNat_spec m
  have e : T = Finset.range m := Finset.eq_of_subset_of_card_le incl (by simpa [card] using h)
  subst T
  have atRange (i : ℕ) (hi : i < m) : i ∈ (Finset.range m : Set ℕ) := Finset.mem_range.mpr hi
  have bad := free (atRange 0 (by omega)) (atRange 1 (by omega))
    (atRange 2 (by omega)) (by decide)
  omega

theorem digit_product {m : ℕ} (hm : 0 < m) {x : ℝ} (hx : 0 ≤ x) :
    (rothNumberNat m : ℝ)*profile x ≤ profile ((2*(m:ℝ)-1)*x) := by
  have nonneg : 0 ≤ profile x := by
    have b := (shape_bounds (by linarith : 0 ≤ 5*x)).1
    unfold profile
    linarith
  have n := rothNumberNat_le m
  rcases eq_or_lt_of_le (show 1 ≤ m by omega) with h|h
  · subst m
    have h₁ : (rothNumberNat 1 : ℝ) ≤ 1 := by exact_mod_cast n
    norm_num only [Nat.cast_one,mul_one,show (2:ℝ)-1=1 by norm_num,one_mul]
    simpa using mul_le_mul_of_nonneg_right h₁ nonneg
  rcases eq_or_lt_of_le (show 2 ≤ m by omega) with h|h
  · subst m
    have h₂ : (rothNumberNat 2 : ℝ) ≤ 2 := by exact_mod_cast n
    have g := (interval_inequalities hx hx).2
    have e : (2*(2:ℝ)-1)*x=x+x+max x x := by rw [max_self]; linarith
    rw [Nat.cast_ofNat, e]
    exact (mul_le_mul_of_nonneg_right h₂ nonneg).trans (by linarith)
  have a := roth_lt (by omega : 3 ≤ m)
  have bound : (rothNumberNat m : ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast a
  have mx : 0 ≤ (2*(m:ℝ)-1)*x := by
    apply mul_nonneg _ hx
    have : (1:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have top := (shape_bounds (by linarith : 0 ≤ 5*x)).2
  have bot := (shape_bounds (by linarith : 0 ≤ 5*((2*(m:ℝ)-1)*x))).1
  unfold profile
  have rpos : 0 ≤ (rothNumberNat m : ℝ) := Nat.cast_nonneg _
  have main := mul_le_mul_of_nonneg_left top rpos
  nlinarith [mul_nonneg (sub_nonneg.mpr bound) hx]

#print axioms monotone
#print axioms plateau
#print axioms interval_inequalities
#print axioms digit_product
end
end Erdos142Scalar
