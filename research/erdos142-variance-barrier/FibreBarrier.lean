import Mathlib.Tactic

namespace FibreBarrier

/-- Secondary energy loses at least one unit on the mixed-lobe family. -/
theorem secondary_loss {a b c : ℝ}
    (ha : -(1/2 : ℝ) ≤ a) (ha' : a ≤ 1/2)
    (hc : -(1/2 : ℝ) ≤ c) (hc' : c ≤ 1/2)
    (h : a+c = 2*b-1) :
    (1+a)^2 + (1+c)^2 - 2*(1+b)^2 ≤ -1 := by
  have h₀ : 0 ≤ b := by linarith
  have h₁ : 0 ≤ (1-(a-c))*(1+(a-c)) :=
    mul_nonneg (by linarith) (by linarith)
  have hb : b=(a+c+1)/2 := by linarith
  rw [hb] at *
  nlinarith

/-- Induction on a finite symmetric stencil, measured in unit steps. -/
theorem slope_growth (f : ℤ → ℝ) (k : ℕ)
    (h : ∀ i : ℤ, -(k : ℤ) < i → i < (k : ℤ) →
      1 ≤ f (i-1) + f (i+1) - 2*f i) :
    (k : ℝ)^2 ≤ f (-(k : ℤ)) + f (k : ℤ) - 2*f 0 := by
  have step (j : ℕ) (hj : j < k) :
      (2*(j:ℝ)+1) ≤ (f (-(j:ℤ)-1) - f (-(j:ℤ))) +
                       (f ((j:ℤ)+1) - f (j:ℤ)) := by
    induction j with
    | zero =>
      simpa using (show 1 ≤ f (-1) - f 0 + (f 1 - f 0) by
        linarith [show 1 ≤ f (-1) + f 1 - 2*f 0 by simpa using h 0 (by omega) (by omega)])
    | succ j ih =>
      have hprev := ih (by omega)
      have hl := h (-((j:ℤ)+1)) (by omega) (by omega)
      have hr := h ((j:ℤ)+1) (by omega) (by omega)
      simp only [Nat.cast_succ]
      simp only [neg_add_rev] at hl ⊢
      convert_to _ ≤ f ((-1 + -(j:ℤ))-1) - f (-1 + -(j:ℤ)) +
                       (f (((j:ℤ)+1)+1) - f ((j:ℤ)+1)) using 1
      have heq : (-1 + -(j:ℤ))+1 = -(j:ℤ) := by omega
      have heq' : (-1 + -(j:ℤ)) = -(j:ℤ)-1 := by omega
      rw [heq] at hl
      rw [show ((j:ℤ)+1)-1 = (j:ℤ) by omega] at hr
      rw [← heq'] at hprev
      linarith
  have total (j : ℕ) (hj : j ≤ k) :
      (j : ℝ)^2 ≤ f (-(j : ℤ)) + f (j : ℤ) - 2*f 0 := by
    induction j with
    | zero => simp
              linarith
    | succ j ih =>
      have hprev := ih (by omega)
      have hs := step j (by omega)
      push_cast
      rw [show -((j:ℤ)+1) = -(j:ℤ)-1 by omega]
      nlinarith
  exact total k le_rfl

end FibreBarrier

namespace FibreBarrier

/-- If either top endpoint maximizes its fibre, both top certificates
    yield a discrete convexity certificate for the moving maximum. -/
theorem envelope_step {a b c d left right fee : ℝ}
    (hf : 0 < fee) (ha : a+fee ≤ max (max a b) (max c d))
    (hb : b+fee ≤ max (max a b) (max c d))
    (hc : 2*c+fee ≤ left+right) (hd : 2*d+fee ≤ left+right) :
    fee ≤ left+right-2*max (max a b) (max c d) := by
  have hlow : max a b + fee ≤ max (max a b) (max c d) := by
    rcases le_total a b with h | h
    · rwa [max_eq_right h] at hb ⊢
    · rwa [max_eq_left h] at ha ⊢
  have hlt : max a b < max c d := by
    by_contra! h
    rw [max_eq_left h] at hlow
    linarith
  rw [max_eq_right hlt.le]
  rcases le_total c d with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

end FibreBarrier
