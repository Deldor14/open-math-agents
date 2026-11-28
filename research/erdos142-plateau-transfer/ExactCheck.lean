import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

open scoped BigOperators Polynomial
open Polynomial

namespace Erdos142Plateau

noncomputable def indicator (S : Finset ℕ) : ℕ[X] := ∑ i ∈ S, X ^ i

def pairs (S : Finset ℕ) (k : ℕ) : Finset (ℕ × ℕ) :=
  (S ×ˢ S).filter fun t => t.1 + t.2 = k

/-- Squaring the indicator polynomial counts ordered endpoint pairs. -/
theorem coeff_square (S : Finset ℕ) (k : ℕ) :
    ((indicator S)^2).coeff k = (pairs S k).card := by
  simp only [indicator, pow_two, Finset.sum_mul, Finset.mul_sum, ← pow_add,
    Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, pairs, Finset.card_filter,
    Finset.sum_product]
  simp_rw [eq_comm (a := k)]
  simp only [Nat.add_comm]

/-- The diagonal is the unique pair at each occupied middle iff the set
contains no nonconstant three-term progression. -/
theorem exact_test (S : Finset ℕ) :
    (∀ y ∈ S, ((indicator S)^2).coeff (2*y) = 1) ↔
      ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x+z = 2*y → x=y := by
  constructor
  · intro h x hx y hy z hz heq
    have hh := (coeff_square S (2*y)).symm.trans (h y hy)
    have hp : (x,z) ∈ pairs S (2*y) := by simp [pairs, hx, hz, heq]
    have hd : (y,y) ∈ pairs S (2*y) := by simp [pairs, hy, two_mul]
    exact congrArg Prod.fst ((Finset.card_le_one.mp hh.le) _ hp _ hd)
  · intro h y hy
    rw [coeff_square]
    apply Finset.card_eq_one.mpr
    refine ⟨(y,y), ?_⟩
    ext ⟨x,z⟩
    simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hx,hz⟩,heq⟩
      have hxy := h x hx y hy z hz heq
      exact ⟨hxy, by omega⟩
    · rintro ⟨rfl,rfl⟩
      exact ⟨⟨hy,hy⟩,by omega⟩

end Erdos142Plateau

#print axioms Erdos142Plateau.coeff_square
#print axioms Erdos142Plateau.exact_test
