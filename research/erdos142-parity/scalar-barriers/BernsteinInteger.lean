import Mathlib

/-! Degree-seven Bernstein coefficients and their signed finite-difference
evaluation. The coefficient estimate for powers keeps the factors ordered. -/

namespace Erdos142Bernstein
open Finset Polynomial
open scoped Polynomial

/-- Bernstein coefficient at the number i of occurrences of the first letter. -/
noncomputable def coeff (i : ℕ) : ℝ :=
  4*(i : ℝ)/7 - 12*(i.choose 2 : ℝ)/21 + 8*(i.choose 3 : ℝ)/35

theorem coeff_bound (i : Fin 8) : |coeff i| ≤ 4/7 := by
  fin_cases i <;> norm_num [coeff, Nat.choose]

theorem cubic_expansion (y : ℝ) :
    4*y - 12*y^2 + 8*y^3 =
      ∑ i : Fin 8, coeff i * ((7 : ℕ).choose i : ℝ) * y^(i : ℕ) * (1-y)^(7-i.val) := by
  norm_num [Fin.sum_univ_succ, coeff, Nat.choose]
  ring

theorem polynomial_expansion :
    4*(X : ℝ[X]) - 12*X^2 + 8*X^3 =
      ∑ i : Fin 8, C (coeff i) * bernsteinPolynomial ℝ 7 i := by
  apply Polynomial.funext
  intro y
  simpa [Polynomial.eval_finsetSum, bernsteinPolynomial, mul_assoc] using cubic_expansion y

/-- D is the difference u(n)-u(n+1). -/
noncomputable def diff (u : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, n => u n
  | h+1, n => diff u h n - diff u h (n+1)

section Functional
variable {A : Type*} [CommRing A] [Algebra ℝ A]

theorem eval_difference (L : A →ₗ[ℝ] ℝ) (y : A) (n h : ℕ) :
    L (y^n*(1-y)^h) = diff (fun j => L (y^j)) h n := by
  induction h generalizing n with
  | zero => simp [diff]
  | succ h ih =>
    rw [diff,←ih,←ih,←map_sub]
    congr 1
    rw [pow_succ, pow_succ y n]
    ring

/-- When x=2y, the factor x^k contributes exactly 2^k. -/
theorem scaled_difference (L : A →ₗ[ℝ] ℝ) {x y : A} (hxy : x = 2*y)
    (u : ℕ → ℝ) (mom : ∀ j, L (y^j) = u j) (k i h : ℕ) :
    L (x^k*y^i*(1-y)^h) = 2^k * diff u h (k+i) := by
  subst x
  have e : (2*y)^k * y^i*(1-y)^h = (2:ℝ)^k • (y^(k+i)*(1-y)^h) := by
    rw [Algebra.smul_def, map_pow, map_ofNat, mul_pow, pow_add]
    ring
  rw [e,map_smul,smul_eq_mul,eval_difference,funext mom]

end Functional

/-- The coefficient of an ordered product of n Bernstein terms is bounded by
γ^n before the terms with equal numbers of letters are combined. -/
theorem word_bound {ι : Type*} {b : ι → ℝ} {γ : ℝ}
    (hb : ∀ i, |b i| ≤ γ) {n : ℕ} (word : Fin n → ι) :
    |∏ j, b (word j)| ≤ γ^n := by
  rw [Finset.abs_prod]
  calc (∏ j, |b (word j)|) ≤ ∏ _j : Fin n, γ :=
      prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => hb (word j))
    _ = γ^n := by simp

/-- Expansion of a power over ordered choices of one term from each factor.
The Bernstein basis can be substituted for B in any commutative real algebra. -/
theorem power_words {ι R : Type*} [Fintype ι] [CommSemiring R]
    (b B : ι → R) (n : ℕ) :
    (∑ i, b i * B i)^n =
      ∑ word : Fin n → ι, (∏ j, b (word j)) * ∏ j, B (word j) := by
  classical
  have e := Fintype.prod_sum (fun (_ : Fin n) (i : ι) => b i * B i)
  simpa only [prod_const, card_univ, Fintype.card_fin, prod_mul_distrib] using e

/-- Exact expansion of every power of the cubic over ordered Bernstein terms. -/
theorem cubic_power_words (n : ℕ) :
    (4*(X : ℝ[X]) - 12*X^2 + 8*X^3)^n =
      ∑ word : Fin n → Fin 8, (∏ j, C (coeff (word j))) *
        ∏ j, bernsteinPolynomial ℝ 7 (word j) := by
  rw [polynomial_expansion]
  exact power_words (fun i : Fin 8 => C (coeff i)) (fun i => bernsteinPolynomial ℝ 7 i) n

theorem cubic_word_bound {n : ℕ} (word : Fin n → Fin 8) :
    |∏ j, coeff (word j)| ≤ (4/7 : ℝ)^n :=
  word_bound (fun i : Fin 8 => coeff_bound i) word

#print axioms coeff_bound
#print axioms polynomial_expansion
#print axioms scaled_difference
#print axioms word_bound
#print axioms cubic_power_words
#print axioms cubic_word_bound
end Erdos142Bernstein
