import Mathlib

/-!
# OEIS A109381: maximum factorial-base digit of n² tends to infinity

Source: https://oeis.org/A109381
`a n` is the maximum digit of `n²` written in the factorial number system. Conjecture:
`a(n) → ∞`.

Conventions. The factorial-base digit of `m` at position `k ≥ 1` is `⌊m / k!⌋ mod (k + 1)`;
the maximum is taken over the positions `k = 1, …, m`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a109381

open Filter

/-- Maximum factorial-base digit of `m`. -/
def maxDigit (m : ℕ) : ℕ := (Finset.Icc 1 m).sup fun k => m / k.factorial % (k + 1)

end OMA.S_oeis_a109381
namespace Deldor14.SparseFactorialDigits
open Finset Nat OMA.S_oeis_a109381 Filter
private def digit (x i : ℕ) := x / (i+1).factorial % (i+2)
private lemma recover (k x y : ℕ) (same : ∀ i < k, digit x i = digit y i) :
    x % (k+1).factorial = y % (k+1).factorial := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    have last := same k (by omega)
    have prev := ih (fun i hi => same i (by omega))
    rw [Nat.factorial_succ (k+1),Nat.mul_comm (k+1+1),Nat.mod_mul,Nat.mod_mul,prev]
    change _ + _ * digit x k = _ + _ * digit y k
    rw [last]
private lemma bounded (x i D : ℕ) (h : maxDigit x ≤ D) : digit x i ≤ D := by
  by_cases hi : i+1 ≤ x
  · exact (Finset.le_sup (f:=fun j => x/j.factorial % (j+1)) (mem_Icc.mpr ⟨by omega,hi⟩)).trans h
  · have small : x < (i+1).factorial := lt_of_lt_of_le (by omega : x < i+1) (Nat.self_le_factorial _)
    simp [digit,Nat.div_eq_of_lt small]
/-- Count of exceptional positive or zero roots below N. -/
def exceptions (D N : ℕ) := ((range N).filter (fun n => maxDigit (n^2) ≤ D)).card
/-- At a given factorial threshold each exceptional square is encoded by k digits in base D+1. -/
theorem words (D N k : ℕ) (hN : N^2 < (k+1).factorial) : exceptions D N ≤ (D+1)^k := by
  let E := (range N).filter (fun n => maxDigit (n^2) ≤ D)
  let encode (n : ↥E) (i : Fin k) : Fin (D+1) :=
    ⟨digit (n.val^2) i.val, Nat.lt_succ_of_le (bounded _ _ _ (mem_filter.mp n.property).2)⟩
  have inj : Function.Injective encode := by
    intro n m eq
    have same := recover k (n.val^2) (m.val^2) (fun i hi => congrArg Fin.val (congrFun eq ⟨i,hi⟩))
    have small (v : ↥E) : v.val^2 < (k+1).factorial :=
      lt_of_le_of_lt (Nat.pow_le_pow_left (mem_range.mp (mem_filter.mp v.property).1).le _) hN
    rw [Nat.mod_eq_of_lt (small n),Nat.mod_eq_of_lt (small m)] at same
    exact Subtype.ext (by nlinarith)
  have card := Fintype.card_le_of_injective encode inj
  simpa [exceptions,E,Fintype.card_fun] using card
private lemma factorial_dominates (B k : ℕ) (hb : 1 ≤ B) (hk : 2*B^2 ≤ k) : B^k ≤ k.factorial := by
  let t:=k/2
  have hd : B^2 ≤ t := by dsimp [t];omega
  have le : t ≤ k := by dsimp [t];omega
  have exp : k ≤ 2*(k-t) := by dsimp [t];omega
  calc
    B^k ≤ B^(2*(k-t)) := Nat.pow_le_pow_right hb exp
    _ = (B^2)^(k-t) := pow_mul ..
    _ ≤ t^(k-t) := Nat.pow_le_pow_left hd _
    _ ≤ t.factorial*t^(k-t) := Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    _ ≤ k.factorial := Nat.factorial_mul_pow_sub_le_factorial le
/-- For every fixed digit bound D, the exceptional roots have subpolynomial counting function. -/
theorem subpolynomial (D M : ℕ) : ∀ᶠ N : ℕ in atTop, (exceptions D N)^M ≤ N := by
  let B:=(D+1)^(2*M)
  let K:=2*B^2
  apply eventually_atTop.mpr
  refine ⟨K.factorial,fun N hN => ?_⟩
  have pos : 1 ≤ N := (Nat.factorial_pos K).trans_le hN
  have n2 : N ≤ N^2 := by nlinarith
  have ok : ∃ j : ℕ, N^2 < (j+1).factorial :=
    ⟨N^2,Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.self_le_factorial _)⟩
  let k:=Nat.find ok
  have big : N^2 < (k+1).factorial := Nat.find_spec ok
  have hk : K ≤ k := by
    by_contra! nh
    have := Nat.factorial_le (show k+1 ≤ K by omega)
    omega
  have low : k.factorial ≤ N^2 := by
    by_cases hz : k=0
    · simp [hz];omega
    have prev := Nat.find_min ok (show k-1 < k by omega)
    simp only [Nat.sub_add_cancel (show 1 ≤ k by omega),not_lt] at prev
    exact prev
  have cap := words D N k big
  have dom := (factorial_dominates B k (by change 0 < (D+1)^(2*M);positivity) hk).trans low
  have powbound := Nat.pow_le_pow_left cap (2*M)
  have swap : ((D+1)^k)^(2*M)=B^k := by dsimp [B];rw [←pow_mul,←pow_mul,Nat.mul_comm]
  rw [swap] at powbound
  have est := powbound.trans dom
  rw [Nat.mul_comm 2 M,pow_mul] at est
  nlinarith
end Deldor14.SparseFactorialDigits
#print axioms Deldor14.SparseFactorialDigits.words
#print axioms Deldor14.SparseFactorialDigits.subpolynomial
