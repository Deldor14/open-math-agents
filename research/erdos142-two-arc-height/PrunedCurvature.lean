import Mathlib

namespace PerforatedBand

def curvature (f : ℤ → ℝ) (x h : ℤ) : ℝ :=
  f (x - h) + f (x + h) - 2 * f x

def triple (S : Set ℤ) (x h : ℤ) : Prop :=
  x - h ∈ S ∧ x ∈ S ∧ x + h ∈ S

theorem subdivision (f : ℤ → ℝ) (x h : ℤ) :
    curvature f x (2*h) =
      curvature f (x-h) h + 2*curvature f x h + curvature f (x+h) h := by
  unfold curvature
  simp only [sub_add_cancel, add_sub_cancel_right]
  rw [show x-h-h = x-2*h by ring, show x+h+h = x+2*h by ring]
  ring

/-- Four times the child average, pruned when a child stencil is missing. -/
noncomputable def retained (S : Set ℤ) (f : ℤ → ℝ) : ℕ → ℤ → ℝ
  | 0, x => by
      classical
      exact if triple S x 1 then curvature f x 1 else 0
  | n+1, x => by
      classical
      let h : ℤ := 2^n
      exact if triple S (x-h) h ∧ triple S x h ∧ triple S (x+h) h then
        retained S f n (x-h) + 2*retained S f n x + retained S f n (x+h)
      else 0

/-- The unnormalized sum of surviving leaf curvatures is bounded by the root. -/
theorem retained_le (S : Set ℤ) (f : ℤ → ℝ)
    (conv : ∀ x h, triple S x h → 0 ≤ curvature f x h) :
    ∀ n x, triple S x (2^n) →
      0 ≤ retained S f n x ∧ retained S f n x ≤ curvature f x (2^n) := by
  classical
  intro n
  induction n with
  | zero =>
      intro x hx
      simp only [pow_zero] at *
      simp [retained, hx, conv x 1 hx]
  | succ n ih =>
      intro x hx
      let h : ℤ := 2^n
      have hs : (2:ℤ)^(n+1) = 2*h := by dsimp [h]; ring
      by_cases ok : triple S (x-h) h ∧ triple S x h ∧ triple S (x+h) h
      · have hl := ih (x-h) ok.1
        have hc := ih x ok.2.1
        have hr := ih (x+h) ok.2.2
        change 0 ≤ retained S f (n+1) x ∧ retained S f (n+1) x ≤ _
        simp only [retained, show (2:ℤ)^n = h from rfl, if_pos ok, hs, subdivision]
        change 0 ≤ retained S f n (x-h) + 2*retained S f n x + retained S f n (x+h) ∧ _ 
        change 0 ≤ retained S f n (x-h) ∧ retained S f n (x-h) ≤ curvature f (x-h) h at hl
        change 0 ≤ retained S f n x ∧ retained S f n x ≤ curvature f x h at hc
        change 0 ≤ retained S f n (x+h) ∧ retained S f n (x+h) ≤ curvature f (x+h) h at hr
        constructor <;> linarith [hl.1, hl.2, hc.1, hc.2, hr.1, hr.2]
      · simp only [retained, show (2:ℤ)^n = h from rfl, if_neg ok, le_refl, true_and]
        exact conv x _ hx

#print axioms subdivision
#print axioms retained_le
end PerforatedBand
