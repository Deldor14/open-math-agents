import FibonacciCarry
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Exact decomposition into binary atoms for the truncated Fibonacci
capacity. The largest atom 2^s may occur as often as necessary. -/

namespace Erdos142ProfileAtoms
open Finset Erdos142FibonacciCarry

/-- Translation by one full period is additive for the truncated capacity. -/
theorem add_period (s j : ℕ) : A s (2^s+j) = A s (2^s)+A s j := by
  unfold A
  have split : (∑ t ∈ range s, c t*((2^s+j)/2^(t+1))) =
      ∑ t ∈ range s, (c t*(2^s/2^(t+1))+c t*(j/2^(t+1))) := by
    apply sum_congr rfl
    intro t ht
    rw [Nat.add_div_of_dvd_right (pow_dvd_pow 2 (mem_range.mp ht)),Nat.mul_add]
  rw [split,sum_add_distrib]
  omega

private theorem below_period {s j : ℕ} (h : j < 2^(s+1)) : A (s+1) j=A s j := by
  simp [next_A, Nat.div_eq_of_lt h]

theorem decomposition (s j : ℕ) : ∃ L : List ℕ,
    (∀ x ∈ L, ∃ k ≤ s, x=2^k) ∧ L.sum=j ∧ (L.map (A s)).sum=A s j := by
  induction s generalizing j with
  | zero =>
    refine ⟨List.replicate j 1,?_,by simp,?_⟩
    · intro x hx
      exact ⟨0,le_rfl,by simpa using List.eq_of_mem_replicate hx⟩
    · simp [A]
  | succ s prev =>
    induction j using Nat.strong_induction_on with
    | h j earlier =>
      by_cases small : j < 2^(s+1)
      · obtain ⟨L,powers,total,weighted⟩ := prev j
        have within (x : ℕ) (hx : x ∈ L) : x < 2^(s+1) := by
          obtain ⟨k,hk,rfl⟩ := powers x hx
          exact Nat.pow_lt_pow_right (by decide : 1<2) (by omega)
        have same := List.map_congr_left (l := L) (fun x hx => below_period (within x hx))
        refine ⟨L,?_,total,?_⟩
        · intro x hx
          obtain ⟨k,hk,e⟩ := powers x hx
          exact ⟨k,by omega,e⟩
        · rw [same,weighted,below_period small]
      · have pos : 0 < 2^(s+1) := by positivity
        obtain ⟨L,powers,total,weighted⟩ := earlier (j-2^(s+1)) (by omega)
        have rebuilt : 2^(s+1)+(j-2^(s+1))=j := by omega
        refine ⟨2^(s+1)::L,?_,?_,?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl|hm
          · exact ⟨s+1,le_rfl,rfl⟩
          · exact powers x hm
        · simpa only [List.sum_cons,total] using rebuilt
        · simp only [List.map_cons,List.sum_cons,weighted]
          rw [← add_period,rebuilt]

theorem seven (j : ℕ) : ∃ L : List ℕ,
    (∀ x ∈ L, ∃ k ≤ 7, x=2^k) ∧ L.sum=j ∧ (L.map (A 7)).sum=A 7 j :=
  decomposition 7 j

#print axioms add_period
#print axioms decomposition
#print axioms seven
end Erdos142ProfileAtoms
