import Mathlib

namespace HalfFibreDescent

def budget (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | k+1 => 2*(ε+budget ε k)

theorem budget_closed (ε : ℝ) (n : ℕ) :
    budget ε n = 2*ε*((2:ℝ)^n-1) := by
  induction n with
  | zero => simp [budget]
  | succ n ih => simp only [budget,ih,pow_succ]; ring

theorem chain_drop (M : ℕ → ℝ) (d : ℝ) (n : ℕ)
    (h : ∀ i < n, M (i+1) ≤ M i - d) :
    M n ≤ M 0 - n*d := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := h n (by omega)
    have ht := ih (fun i hi => h i (by omega))
    push_cast
    linarith

theorem width_cost (M : ℕ → ℝ) (d c K : ℝ) (n : ℕ)
    (hM : M 0 ≤ K) (hn : 0 ≤ M n)
    (h : ∀ i < n, M (i+1) ≤ M i - c*d^2/2) :
    n*c*d^2 ≤ 2*K := by
  have ht := chain_drop M (c*d^2/2) n h
  linarith only [show (n:ℝ)*(c*d^2/2)=n*c*d^2/2 by ring, ht,hM,hn]

theorem quantile_drop (M : ℕ → ℝ) (d c ω : ℝ) (n : ℕ)
    (hgap : M 0 - M n ≤ ω)
    (h : ∀ i < n, M (i+1) ≤ M i - c*d^2/2) :
    n*c*d^2 ≤ 2*ω := by
  have ht := chain_drop M (c*d^2/2) n h
  linarith only [show (n:ℝ)*(c*d^2/2)=n*c*d^2/2 by ring, ht,hgap]

theorem volume_decimal : (53:ℝ)/320+1/500=1341/8000 := by norm_num

#print axioms budget_closed
#print axioms chain_drop
#print axioms width_cost
#print axioms quantile_drop
#print axioms volume_decimal
end HalfFibreDescent
