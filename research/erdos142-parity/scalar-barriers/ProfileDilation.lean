import ProfileAtoms
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic

namespace Erdos142ProfileDilation
open Erdos142FibonacciCarry Finset

/-- The right limit of the lower inverse of the continuous profile. -/
noncomputable def P (s : ℕ) (x : ℝ) : ℝ :=
  x + ∑ i ∈ range s, (c i : ℝ)*(⌊x/(↑(2^(i+1):ℕ):ℝ)⌋₊ : ℝ)

theorem P_decompose (s : ℕ) (x : ℝ) :
    P s x = (A s ⌊x⌋₊ : ℝ) + (x-⌊x⌋₊) := by
  simp only [P,A,Nat.floor_div_natCast,Nat.cast_add,Nat.cast_sum,Nat.cast_mul]
  ring

@[simp] theorem P_nat (s j : ℕ) : P s j = (A s j : ℝ) := by
  simp [P_decompose]

theorem P_ge (s : ℕ) (x : ℝ) : x ≤ P s x := by
  unfold P
  exact le_add_of_nonneg_right (sum_nonneg (fun i _ => by positivity))

theorem P_super (s : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    P s x + P s y ≤ P s (x+y) := by
  have comp (i : ℕ) : ⌊x/(↑(2^(i+1):ℕ):ℝ)⌋₊ + ⌊y/(↑(2^(i+1):ℕ):ℝ)⌋₊ ≤
      ⌊(x+y)/(↑(2^(i+1):ℕ):ℝ)⌋₊ := by
    rw [add_div]
    apply Nat.le_floor
    push_cast
    exact add_le_add (Nat.floor_le (by positivity)) (Nat.floor_le (by positivity))
  have le := sum_le_sum (s := range s) (fun i _ =>
    mul_le_mul_of_nonneg_left (show
      (⌊x/(↑(2^(i+1):ℕ):ℝ)⌋₊ : ℝ) + ⌊y/(↑(2^(i+1):ℕ):ℝ)⌋₊ ≤
      ⌊(x+y)/(↑(2^(i+1):ℕ):ℝ)⌋₊ by exact_mod_cast comp i) (Nat.cast_nonneg (α := ℝ) (c i)))
  simp only [mul_add,sum_add_distrib] at le
  unfold P
  linarith

theorem finite_test (s : ℕ) {r L : ℝ} (hr : 1 ≤ r) (hL : r ≤ L) :
    (∀ x : ℝ, 0 ≤ x → P s x ≤ L*P s (x/r)) ↔
    (∀ k : ℕ, k ≤ s → (A s (2^k) : ℝ) ≤ L*P s ((2:ℝ)^k/r)) := by
  have rp : 0 < r := by linarith
  have lp : 0 ≤ L := by linarith
  constructor
  · intro all k _
    simpa only [← Nat.cast_ofNat (R := ℝ) (n := 2), ← Nat.cast_pow, P_nat] using
      all (↑(2^k:ℕ)) (by positivity)
  · intro test x hx
    have lift_list (D : List ℕ) (atoms : ∀ u ∈ D, ∃ k ≤ s, u=2^k) :
        ((D.map (A s)).sum : ℝ) ≤ L*P s ((D.sum : ℝ)/r) := by
      induction D with
      | nil => simp [P]
      | cons d D ih =>
        obtain ⟨k,hk,rfl⟩ := atoms d (by simp)
        have rest := ih (fun u hu => atoms u (List.mem_cons_of_mem _ hu))
        have first := test k hk
        have both := mul_le_mul_of_nonneg_left (P_super s
          (show 0 ≤ (2:ℝ)^k/r by positivity) (show 0 ≤ (D.sum:ℝ)/r by positivity)) lp
        simp only [List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,add_div]
        linarith
    let j := ⌊x⌋₊
    obtain ⟨D,atoms,integer,weight⟩ := Erdos142ProfileAtoms.decomposition s j
    have main := lift_list D atoms
    rw [weight,integer] at main
    have hz : 0 ≤ x-(j:ℝ) := sub_nonneg.mpr (Nat.floor_le hx)
    have hrule : x-(j:ℝ) ≤ L*P s ((x-j)/r) := by
      have h := mul_le_mul_of_nonneg_right hL (div_nonneg hz rp.le)
      calc x-(j:ℝ) = r*((x-j)/r) := by field_simp
           _ ≤ L*((x-j)/r) := h
           _ ≤ _ := mul_le_mul_of_nonneg_left (P_ge _ _) lp
    have add := mul_le_mul_of_nonneg_left (P_super s (show 0 ≤ (j:ℝ)/r by positivity)
      (show 0 ≤ (x-j)/r from div_nonneg hz rp.le)) lp
    rw [← add_div, show (j:ℝ)+(x-j)=x by ring] at add
    rw [P_decompose]
    change (A s j:ℝ)+(x-j) ≤ _
    linarith

#print axioms finite_test
end Erdos142ProfileDilation
