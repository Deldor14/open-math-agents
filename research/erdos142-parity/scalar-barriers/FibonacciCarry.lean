import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Binary-floor sums with Fibonacci weights. The weight indexed by t here is
the coefficient of floor(j / 2^(t+1)), i.e. c_(t+1) in one-based notation. -/

namespace Erdos142FibonacciCarry
open Finset

def w (s : ℕ) : ℕ := Nat.fib (2*s+2)
def c (t : ℕ) : ℕ := Nat.fib (2*t+1)
def A (s j : ℕ) : ℕ := j + ∑ t ∈ range s, c t * (j / 2^(t+1))

theorem next_c (s : ℕ) : c (s+1) = c s + w s := by
  unfold w c
  simpa only [show 2*(s+1)+1 = (2*s+1)+2 by omega,
    show 2*s+1+1=2*s+2 by omega] using (@Nat.fib_add_two (2*s+1))

theorem next_w (s : ℕ) : w (s+1) = w s + c (s+1) := by
  unfold w c
  simpa only [show 2*(s+1)+2=(2*s+2)+2 by omega,
    show 2*(s+1)+1=(2*s+2)+1 by omega] using (@Nat.fib_add_two (2*s+2))

theorem weight_difference (s : ℕ) : c s = w (s+1)-2*w s := by
  rw [next_w, next_c]
  omega

theorem cumulative_weight (h : ℕ) : ∑ t ∈ range (h+1), c t = w h := by
  induction h with
  | zero => decide
  | succ h ih => rw [sum_range_succ, ih, next_w]

theorem next_A (s j : ℕ) : A (s+1) j = A s j + c s*(j/2^(s+1)) := by
  simp [A,sum_range_succ,Nat.add_assoc]

theorem monotone (s : ℕ) : Monotone (A s) := by
  intro x y h
  exact Nat.add_le_add h <| sum_le_sum (fun t _ => Nat.mul_le_mul_left _ (Nat.div_le_div_right h))

/-- Evaluation on the truncation's dyadic scale is exact. -/
theorem at_power (s : ℕ) : A s (2^s) = w s := by
  induction s with
  | zero => decide
  | succ s ih =>
    have double : A s (2^(s+1)) = 2*A s (2^s) := by
      change 2^(s+1)+(∑ t ∈ range s, c t*(2^(s+1)/2^(t+1))) =
        2*(2^s + ∑ t ∈ range s, c t*(2^s/2^(t+1)))
      rw [Nat.mul_add,mul_sum,show 2^(s+1) = 2*2^s by rw [pow_succ,Nat.mul_comm]]
      apply congrArg ((2*2^s)+·)
      apply sum_congr rfl
      intro t ht
      have dvd : 2^(t+1) ∣ 2^s := pow_dvd_pow _ (mem_range.mp ht)
      rw [Nat.mul_div_assoc 2 dvd]
      ring
    rw [next_A,double,ih,Nat.div_self (by positivity),Nat.mul_one,next_w,next_c]
    omega

private theorem floor_lower (i j d : ℕ) (hd : 0 < d) :
    i/d+j/d ≤ (i+j)/d := by
  apply (Nat.le_div_iff_mul_le hd).mpr
  rw [Nat.add_mul]
  exact Nat.add_le_add (Nat.div_mul_le_self i d) (Nat.div_mul_le_self j d)

theorem superadditive (s i j : ℕ) : A s i + A s j ≤ A s (i+j) := by
  have le := sum_le_sum (s := range s) (fun t _ =>
    Nat.mul_le_mul_left (c t) (floor_lower i j (2^(t+1)) (by positivity)))
  simp only [Nat.mul_add,sum_add_distrib] at le
  unfold A
  omega

private theorem floor_upper (i j d : ℕ) (hd : 0 < d) :
    (i+j+1)/d ≤ i/d+j/d+1 := by
  have x := Nat.mod_add_div i d
  have y := Nat.mod_add_div j d
  have u := Nat.mod_lt i hd
  have v := Nat.mod_lt j hd
  have target : (i+j+1)/d < i/d+j/d+2 := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    rw [Nat.add_mul,Nat.add_mul,Nat.mul_comm (i/d) d,Nat.mul_comm (j/d) d]
    omega
  omega

/-- Only positions at or below the next binary digit of j can carry. -/
private theorem digit_upper {i j : ℕ} (ij : i ≤ j) (t : ℕ) :
    (i+j+1)/2^(t+1) ≤ i/2^(t+1)+j/2^(t+1)+(if 2^t ≤ j then 1 else 0) := by
  split_ifs with h
  · exact floor_upper _ _ _ (by positivity)
  · have z : i+j+1 < 2^(t+1) := by rw [pow_succ];omega
    rw [Nat.div_eq_of_lt z]
    exact Nat.zero_le _

/-- The sum of every weight which could carry is paid for by A_s(j). -/
theorem carry_budget (s j : ℕ) :
    (∑ t ∈ range s, if 2^t ≤ j then c t else 0) ≤ A s j := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [sum_range_succ, next_A]
    by_cases hj : 2^s ≤ j
    · have all (t : ℕ) (ht : t ∈ range s) : 2^t ≤ j :=
        (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_lt (mem_range.mp ht))).trans hj
      have eq : (∑ t ∈ range s, if 2^t ≤ j then c t else 0) = ∑ t ∈ range s, c t :=
        sum_congr rfl (fun t ht => if_pos (all t ht))
      rw [eq,if_pos hj]
      have sum := cumulative_weight s
      rw [sum_range_succ] at sum
      rw [sum, ← at_power]
      exact le_trans (monotone s hj) (Nat.le_add_right _ _)
    · rw [if_neg hj,Nat.add_zero]
      exact ih.trans (Nat.le_add_right _ _)

theorem upper_carry (s : ℕ) {i j : ℕ} (ij : i ≤ j) :
    A s (i+j+1) ≤ A s i + 2*A s j + 1 := by
  have le := sum_le_sum (s := range s) (fun t _ => Nat.mul_le_mul_left (c t) (digit_upper ij t))
  simp only [Nat.mul_add,sum_add_distrib,mul_ite,mul_one,mul_zero] at le
  have budget := carry_budget s j
  unfold A at *
  omega

#print axioms at_power
#print axioms superadditive
#print axioms upper_carry
end Erdos142FibonacciCarry
