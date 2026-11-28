import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.Tactic.Linarith

/-! Splicing an arbitrary finite prefix of integer Roth numbers to a
ceiling-linear tail while preserving splitting, exact gluing, and digits. -/

namespace Erdos142FinitePrefix
open Filter Asymptotics

def B (R : ℕ → ℕ) (p n : ℕ) : ℕ := max (R n) (n ⌈/⌉ p)

private theorem covers {p : ℕ} (hp : 0 < p) (n : ℕ) : n ≤ p*(n ⌈/⌉ p) :=
  (ceilDiv_le_iff_le_mul hp).mp le_rfl

private theorem excess {p : ℕ} (hp : 0 < p) (n : ℕ) : p*(n ⌈/⌉ p) < n+p := by
  rw [Nat.ceilDiv_eq_add_pred_div,Nat.mul_comm]
  have h := Nat.div_mul_le_self (n+p-1) p
  omega

private theorem before_ceil {p n t : ℕ} (hp : 0 < p) :
    t < n ⌈/⌉ p ↔ p*t < n := by
  rw [← not_le,ceilDiv_le_iff_le_mul hp,not_le]

private theorem below_ceil {p n t : ℕ} (hp : 0 < p) (h : p*t < n+p) :
    t ≤ n ⌈/⌉ p := by
  by_contra! bad
  have z := Nat.mul_le_mul_left p (show n ⌈/⌉ p+1 ≤ t by omega)
  rw [Nat.mul_succ] at z
  have cover := covers hp n
  omega

theorem dominates (R : ℕ → ℕ) (p n : ℕ) : R n ≤ B R p n := le_max_left _ _

theorem agrees_on_prefix {R : ℕ → ℕ} {p n : ℕ} (hp : 0<p)
    (pos : ∀ i, 0 < i → 0 < R i) (hn : n ≤ p) : B R p n = R n := by
  apply max_eq_left
  by_cases z : n=0
  · simp [z]
  · apply le_trans (b := 1)
    · exact (ceilDiv_le_iff_le_mul hp).mpr (by simpa using hn)
    · exact pos n (by omega)

theorem monotone {R : ℕ → ℕ} {p : ℕ} (hp : 0<p) (mono : Monotone R) :
    Monotone (B R p) := fun _ _ h => max_le_max (mono h) ((gc_mul_ceilDiv hp).monotone_l h)

theorem subadditive {R : ℕ → ℕ} {p : ℕ} (hp : 0<p)
    (sub : ∀ a b, R (a+b) ≤ R a+R b) (a b : ℕ) :
    B R p (a+b) ≤ B R p a+B R p b := by
  apply max_le
  · exact (sub a b).trans (Nat.add_le_add (le_max_left _ _) (le_max_left _ _))
  · apply le_trans (b := (a ⌈/⌉ p)+(b ⌈/⌉ p))
    · apply (ceilDiv_le_iff_le_mul hp).mpr
      rw [Nat.mul_add]
      exact Nat.add_le_add (covers hp a) (covers hp b)
    · exact Nat.add_le_add (le_max_right _ _) (le_max_right _ _)

theorem step {R : ℕ → ℕ} {p : ℕ} (hp : 0<p) (one : R 1 ≤ 1)
    (sub : ∀ a b, R (a+b) ≤ R a+R b) (n : ℕ) : B R p (n+1) ≤ B R p n+1 := by
  apply (subadditive hp sub n 1).trans
  apply Nat.add_le_add_left
  exact max_le one ((ceilDiv_le_iff_le_mul hp).mpr (by simpa using (show 1 ≤ p by omega)))

private theorem block_cover {R : ℕ → ℕ} (zero : R 0=0) (mono : Monotone R)
    (sub : ∀ a b, R (a+b) ≤ R a+R b) {a : ℕ} (ha : 0<a) (b : ℕ) :
    R b ≤ (b ⌈/⌉ a)*R a := by
  have mulBound (t : ℕ) : R (a*t) ≤ t*R a := by
    induction t with
    | zero => simp [zero]
    | succ t ih =>
      rw [Nat.mul_succ,Nat.succ_mul]
      exact (sub _ _).trans (Nat.add_le_add_right ih _)
  exact (mono (covers ha b)).trans (mulBound _)

/-- The mixed cases use b≥a. If the ceiling wins at a, subadditivity
bounds R b by a cover consisting of ceil(b/a) translates of [1,a]. -/
theorem exact_glue {R : ℕ → ℕ} {p a b : ℕ} (hp : 0<p)
    (zero : R 0=0) (pos : ∀ n, 0<n → 0 < R n) (mono : Monotone R)
    (sub : ∀ x y, R (x+y) ≤ R x+R y)
    (glue : ∀ x y, 0<x → x≤y → R x+R y ≤ R (x+2*y-1))
    (ha : 0<a) (ab : a≤b) : B R p a+B R p b ≤ B R p (a+2*b-1) := by
  have hb := ha.trans_le ab
  by_cases la : a ⌈/⌉ p ≤ R a
  · rw [B,max_eq_left la]
    by_cases lb : b ⌈/⌉ p ≤ R b
    · rw [B,max_eq_left lb]
      exact (glue a b ha ab).trans (dominates _ _ _)
    · rw [B,max_eq_right (by omega : R b ≤ b ⌈/⌉ p)]
      apply le_trans _ (le_max_right _ _)
      apply below_ceil hp
      have small := (before_ceil hp).mp (lt_of_le_of_lt (mono ab) (by omega : R b < b ⌈/⌉ p))
      have cap := excess hp b
      rw [Nat.mul_add]
      omega
  · rw [B,max_eq_right (by omega : R a ≤ a ⌈/⌉ p)]
    by_cases lb : b ⌈/⌉ p ≤ R b
    · rw [B,max_eq_left lb]
      have small : p*R a < a := (before_ceil hp).mp (by omega)
      have cover := Nat.mul_le_mul_left p (block_cover zero mono sub ha b)
      have scal := Nat.mul_le_mul_left (b ⌈/⌉ a) small.le
      have cap := excess ha b
      have cost : p*R b < 2*b := by nlinarith
      apply le_trans _ (le_max_right _ _)
      apply below_ceil hp
      rw [Nat.mul_add]
      have e := excess hp a
      omega
    · rw [B,max_eq_right (by omega : R b ≤ b ⌈/⌉ p)]
      have psmall : p < b := by
        by_contra! bad
        have z : b ⌈/⌉ p ≤ 1 := (ceilDiv_le_iff_le_mul hp).mpr (by simpa using bad)
        have r := pos b hb
        omega
      apply le_trans _ (le_max_right _ _)
      apply below_ceil hp
      rw [Nat.mul_add]
      have ca := excess hp a
      have cb := excess hp b
      omega

theorem digits {R : ℕ → ℕ} {m p n : ℕ} (hp : 0<p) (hm : 0<m)
    (pos : ∀ i, 0 < i → 0 < R i) (size : R m ≤ m)
    (original : R m*R n ≤ R ((2*m-1)*n)) :
    R m*B R p n ≤ B R p ((2*m-1)*n) := by
  by_cases ln : n ⌈/⌉ p ≤ R n
  · rw [B,max_eq_left ln]
    exact original.trans (dominates _ _ _)
  rw [B,max_eq_right (by omega : R n ≤ n ⌈/⌉ p)]
  apply le_trans _ (le_max_right _ _)
  by_cases one : m=1
  · subst m
    simpa using Nat.mul_le_mul_right (n ⌈/⌉ p) size
  have nz : 0<n := by by_contra! h; simp [show n=0 by omega] at ln
  have kpos : 2 ≤ n ⌈/⌉ p := by have h := pos n nz; omega
  let k := n ⌈/⌉ p
  have en : p*(k-1)<n := (before_ceil hp).mp (by change k-1<k; omega)
  have lm : 2 ≤ m := by omega
  have q : 0<2*m-1 := by omega
  have price : m*k-1 ≤ (2*m-1)*(k-1) := by
    obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le lm
    obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le kpos
    change k=2+v at hv
    rw [hu,hv,Nat.sub_le_iff_le_add,show 2*(2+u)-1=3+2*u by omega,
      show 2+v-1=1+v by omega]
    nlinarith
  apply le_trans (Nat.mul_le_mul_right _ size)
  change m*k ≤ (2*m-1)*n ⌈/⌉ p
  have paid := lt_of_le_of_lt (Nat.mul_le_mul_left p price) (show p*((2*m-1)*(k-1)) < (2*m-1)*n by
    have z := Nat.mul_lt_mul_of_pos_left en q
    simpa only [Nat.mul_left_comm] using z)
  have mkpos : 0<m*k := Nat.mul_pos hm (by omega)
  have z := (before_ceil hp).mpr paid
  omega

/-- Roth's density theorem yields the actual eventual ceiling-linear tail. -/
theorem roth_tail {p : ℕ} (hp : 0<p) :
    ∀ᶠ n in atTop, B rothNumberNat p n = n ⌈/⌉ p := by
  have rp : 0 < (p:ℝ) := by exact_mod_cast hp
  have h := (isLittleO_iff.mp rothNumberNat_isLittleO_id) (show 0 < (p:ℝ)⁻¹ by positivity)
  simp only [RCLike.norm_natCast] at h
  filter_upwards [h] with n hn
  have bound : (p:ℝ)*(rothNumberNat n : ℝ) ≤ (n:ℝ) := by
    have t := mul_le_mul_of_nonneg_left hn rp.le
    simpa [← mul_assoc,ne_of_gt rp] using t
  have hn' : p*rothNumberNat n ≤ n := by exact_mod_cast bound
  exact max_eq_right (below_ceil hp (by omega))

#print axioms exact_glue
#print axioms digits
#print axioms roth_tail
end Erdos142FinitePrefix
