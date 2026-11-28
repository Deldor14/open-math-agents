import Mathlib

/-! Bernstein certificate on [0,2] for the integer polynomial
x^232 (x-2)^132 (x-1)^16 (x^2-3x+3)^5, represented in degree 406. -/

namespace Erdos142ConeCyclotomic
set_option exponentiation.threshold 512
open Finset Polynomial
open scoped Polynomial

def index (j : Fin 22) : ℕ := 232+2*j.val

/-- Coefficients of (U-V)^16 (U+3V)^5 in U^j V^(21-j). -/
def raw (j : Fin 22) : ℤ :=
  ![243, -3483, 22950, -91710, 246435, -464963, 619688, -560520, 289990, 650, -126204, 87724, -12610, -16350, 9320, -200, -1305, 305, 70, -30, -1, 1] j

noncomputable def coeff (j : Fin 22) : ℝ :=
  2^364*(raw j:ℝ)/(Nat.choose 406 (index j):ℝ)

theorem convolution (u v : ℝ) : (u-v)^16*(u+3*v)^5 =
    ∑ j : Fin 22, (raw j:ℝ)*u^(j.val)*v^(21-j.val) := by
  norm_num [Fin.sum_univ_succ,raw]
  ring

theorem order (j : Fin 22) : 4*(406-index j) ≤ 3*index j := by unfold index;omega

private theorem fits (j : Fin 22) : index j ≤ 406 := by have := j.isLt;unfold index;omega

set_option maxRecDepth 10000 in
private theorem certificate : ∀ j : Fin 22,
    200*2^364*(raw j).natAbs < 199*Nat.choose 406 (index j) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

theorem norm_bound (j : Fin 22) : |coeff j| < 199/200 := by
  have h := certificate j
  have hp : (0:ℝ) < Nat.choose 406 (index j) := by exact_mod_cast Nat.choose_pos (fits j)
  unfold coeff
  rw [abs_div, abs_mul, abs_of_pos hp, abs_of_pos (by positivity : (0:ℝ) < 2^364)]
  apply (div_lt_div_iff₀ hp (by norm_num : (0:ℝ) < 200)).2
  have hr : (200:ℝ)*2^364*|(raw j:ℝ)| < 199*(Nat.choose 406 (index j):ℝ) := by
    rw [←Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast]
    exact_mod_cast h
  linarith only [hr]

theorem scalar_expansion (y : ℝ) :
    (2*y)^232*(2*y-2)^132*(2*y-1)^16*((2*y)^2-3*(2*y)+3)^5 =
      ∑ j : Fin 22, coeff j*(Nat.choose 406 (index j):ℝ)*
        y^(index j)*(1-y)^(406-index j) := by
  let z := 1-y
  have shape : (2*y)^232*(2*y-2)^132*(2*y-1)^16*((2*y)^2-3*(2*y)+3)^5 =
    (2^364*y^232*z^132)*((y^2-z^2)^16*(y^2+3*z^2)^5) := by
    rw [show 2*y-2=-(2*z) by dsimp [z];ring,
      show 2*y-1=y^2-z^2 by dsimp [z];ring,
      show (2*y)^2-3*(2*y)+3=y^2+3*z^2 by dsimp [z];ring,
      Even.neg_pow (by decide : Even 132), mul_pow, mul_pow,
      show (2:ℝ)^364=2^232*2^132 by rw [←pow_add]]
    exact (show ∀ a b c d e f : ℝ, (a*b)*(c*d)*e*f = (a*c*b*d)*(e*f) by
      intros; ring) _ _ _ _ _ _
  rw [shape,convolution,mul_sum]
  apply sum_congr rfl
  intro j _
  have hp : (0:ℝ) < Nat.choose 406 (index j) := by exact_mod_cast Nat.choose_pos (fits j)
  have e : 406-index j=132+2*(21-j.val) := by have := j.isLt;unfold index;omega
  rw [coeff,div_mul_cancel₀ _ hp.ne',e]
  change _ = _*y^(232+2*j.val)*z^(132+2*(21-j.val))
  simp only [pow_add,pow_mul]
  ac_rfl

theorem polynomial_expansion :
    (2*X:ℝ[X])^232*(2*X-2)^132*(2*X-1)^16*((2*X)^2-3*(2*X)+3)^5 =
      ∑ j : Fin 22, C (coeff j)*bernsteinPolynomial ℝ 406 (index j) := by
  apply Polynomial.funext
  intro y
  simpa [Polynomial.eval_finsetSum,bernsteinPolynomial,mul_assoc] using scalar_expansion y

#print axioms convolution
#print axioms order
#print axioms norm_bound
#print axioms polynomial_expansion
end Erdos142ConeCyclotomic
