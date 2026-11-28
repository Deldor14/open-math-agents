import ScaleSteps

/-! Quantitative Fibonacci propagation for a scalar function on the integer
grid. The seed may be charged to either endpoint of the outer interval.
The unit-step bound uses the verified two-interval inequality in ScaleSteps. -/

namespace Erdos142Subgolden

def orbit (a b : ℕ) : ℕ → ℕ × ℕ
  | 0 => (a,b)
  | s+1 =>
    let p := orbit a b s
    (p.1+p.2, p.1+2*p.2+1)

def loss (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | s+1 =>
    let p := orbit a b s
    (2*loss a b s+1)*(p.2-p.1)

theorem increasing_after_step (a b s : ℕ) :
    (orbit a b (s+1)).1 < (orbit a b (s+1)).2 := by
  simp only [orbit]
  omega

theorem loss_pos {a b : ℕ} (ab : a < b) (s : ℕ) : 0 < loss a b (s+1) := by
  have sorted : (orbit a b s).1 < (orbit a b s).2 := by
    cases s with
    | zero => exact ab
    | succ s => exact increasing_after_step a b s
  exact Nat.mul_pos (by omega) (Nat.sub_pos_of_lt sorted)

variable (F : ℕ → ℤ) (mono : Monotone F)
    (sub : ∀ x y, F (x+y) ≤ F x + F y)
    (glue : ∀ x y, y ≤ x → F x + F y ≤ F (2*x+y))

include mono sub glue

/-- Unit steps telescope on [a,b]. An initially reversed interval is
permitted: its signed difference is nonpositive and the truncated cost is zero. -/
theorem chain (a b : ℕ) :
    F b-F a ≤ ((b-a : ℕ) : ℤ) * (F (a+2*b+1)-F (a+b)) := by
  by_cases ba : b ≤ a
  · rw [Nat.sub_eq_zero_of_le ba, Nat.cast_zero, zero_mul]
    exact sub_nonpos.mpr (mono ba)
  let D := F (a+2*b+1)-F (a+b)
  have telescopes (n : ℕ) (fits : a+n ≤ b) :
      F (a+n)-F a ≤ (n:ℤ)*D := by
    induction n with
    | zero => simp
    | succ n ih =>
      specialize ih (by omega)
      let x := a+n
      have low : a ≤ x := by dsimp [x];omega
      have room : x+1 ≤ b := by dsimp [x];omega
      have hx : x ≤ a+b := by omega
      have maxBound : max (x+1) (a+b-x) ≤ b := max_le room (by omega)
      have step := Erdos142ScaleSteps.one_step F mono sub glue
        (a+b) (a+2*b+1) x (x+1) hx (by omega)
      change F (x+1)-F a ≤ ((n+1:ℕ):ℤ)*D
      change F x-F a ≤ (n:ℤ)*D at ih
      change F (x+1)-F x ≤ D at step
      rw [Nat.cast_add, Nat.cast_one, add_mul,one_mul]
      linarith
  have finish : a+(b-a)=b := by omega
  simpa only [finish] using telescopes (b-a) (by omega)

/-- The compressed outer value is bounded above by the cost of the initial
block and the accumulated gap. Equivalently this is a lower bound on the
outer gap once the initial value is bounded by a digit seed. -/
theorem propagation (a b s : ℕ) :
    F (orbit a b s).1 ≤ (2:ℤ)^s*F a +
      (loss a b s : ℤ)*(F (orbit a b s).2-F (orbit a b s).1) := by
  induction s with
  | zero => simp [orbit,loss]
  | succ s ih =>
    let p := orbit a b s
    let E : ℤ := loss a b s
    let D := F p.2-F p.1
    let nextD := F (p.1+2*p.2+1)-F (p.1+p.2)
    let m : ℤ := (p.2-p.1 : ℕ)
    change F p.1 ≤ (2:ℤ)^s*F a+E*D at ih
    have pair := sub p.1 p.2
    have high : F (p.1+p.2) ≤ 2*F p.1 + D := by dsimp [D];linarith
    have step : D ≤ m*nextD := chain F mono sub glue p.1 p.2
    have posE : 0 ≤ 2*E+1 := by dsimp [E]; positivity
    have weighted := mul_le_mul_of_nonneg_left step posE
    change F (p.1+p.2) ≤ (2:ℤ)^(s+1)*F a +
      (((2*loss a b s+1)*(p.2-p.1):ℕ):ℤ)*nextD
    push_cast
    change F (p.1+p.2) ≤ (2:ℤ)^(s+1)*F a+(2*E+1)*m*nextD
    rw [pow_succ]
    nlinarith only [ih,high,weighted]

/-- Seed bounded by the left endpoint: no 2^s loss in the final coefficient. -/
theorem left_seed (a b s C : ℕ)
    (seed : (C:ℤ)*F a ≤ F (orbit a b s).1) :
    ((C:ℤ)-(2:ℤ)^s)*F (orbit a b s).1 ≤
      (C:ℤ)*(loss a b s:ℤ)*(F (orbit a b s).2-F (orbit a b s).1) := by
  have h := mul_le_mul_of_nonneg_left (propagation F mono sub glue a b s) (Int.natCast_nonneg C)
  have g := mul_le_mul_of_nonneg_left seed (show 0 ≤ (2:ℤ)^s by positivity)
  nlinarith only [h,g]

/-- Use the extra room up to the right endpoint to pay for the seed. -/
theorem right_seed (a b s C : ℕ)
    (seed : (C:ℤ)*F a ≤ F (orbit a b s).2) :
    ((C:ℤ)-(2:ℤ)^s)*F (orbit a b s).1 ≤
      ((C:ℤ)*(loss a b s:ℤ)+(2:ℤ)^s)*(F (orbit a b s).2-F (orbit a b s).1) := by
  have h := mul_le_mul_of_nonneg_left (propagation F mono sub glue a b s) (Int.natCast_nonneg C)
  have g := mul_le_mul_of_nonneg_left seed (show 0 ≤ (2:ℤ)^s by positivity)
  nlinarith only [h,g]

/-- A positive relative gain, in division-free form. The denominator is
C E_s+2^s>0. This version covers both choices of the initial interval. -/
theorem relative_gain (a b s C : ℕ) (surplus : 2^s < C)
    (seed : (C:ℤ)*F a ≤ F (orbit a b s).2) :
    F (orbit a b s).1 ≤
      ((C:ℤ)*(loss a b s:ℤ)+(2:ℤ)^s)*(F (orbit a b s).2-F (orbit a b s).1) := by
  have h := right_seed F mono sub glue a b s C seed
  have f0 : 0 ≤ F 0 := by have o := sub 0 0; simp only [Nat.add_zero] at o;omega
  have f : 0 ≤ F (orbit a b s).1 := f0.trans (mono (Nat.zero_le _))
  have extra : (2:ℤ)^s < C := by exact_mod_cast surplus
  have coeff : (1:ℤ) ≤ (C:ℤ)-2^s := by omega
  exact le_trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right coeff f) h

#print axioms chain
#print axioms propagation
#print axioms left_seed
#print axioms right_seed
#print axioms relative_gain
end Erdos142Subgolden
