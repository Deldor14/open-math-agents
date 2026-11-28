import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The twist m = 25 in B. Poonen, Acta Arithmetica 86 (1998), section 4.
The first theorem starts with the precise equality in the Left to Solve leaf
BealConjecture.beal_conjecture.R2.H3.R1.H2.R1.H2.R1.H2.
-/
namespace BealQuinticCubic

def quartic (x : ℚ) : ℚ :=
  x^4 + 50*x^3 + 1250*x^2 + 15625*x + 78125

theorem model_iff (v s t : ℕ) (hs : 0 < s) :
    (let d := 25*s^3
     5*v^4 + d*(10*v^3 + 10*v^2*d + 5*v*d^2 + d^3) = 5*t^3) ↔
    ((t : ℚ) / (s : ℚ)^4)^3 = quartic ((v : ℚ) / (s : ℚ)^3) := by
  have hsn : (s : ℚ) ≠ 0 := by positivity
  let d := 25*s^3
  change (5*v^4 + d*(10*v^3 + 10*v^2*d + 5*v*d^2 + d^3) = 5*t^3) ↔ _
  let V : ℚ := v
  let S : ℚ := s
  let T : ℚ := t
  have hS : S ≠ 0 := hsn
  have alg : (T / S^4)^3 = quartic (V / S^3) ↔
      5*V^4 + (25*S^3) * (10*V^3 + 10*V^2*(25*S^3) +
        5*V*(25*S^3)^2 + (25*S^3)^3) = 5*T^3 := by
    unfold quartic
    field_simp [hS]
    constructor <;> intro h <;> linarith only [h]
  rw [show ((t : ℚ) / (s : ℚ)^4)^3 = quartic ((v : ℚ) / (s : ℚ)^3) ↔ _ from alg]
  dsimp [V,S,T,d]
  exact_mod_cast (Iff.rfl : (5*v^4 + 25*s^3*(10*v^3+10*v^2*(25*s^3)+5*v*(25*s^3)^2+(25*s^3)^3)=5*t^3) ↔ _)

theorem quartic_involution (x : ℚ) : quartic (-25-x) = quartic x := by
  unfold quartic
  ring

/-- The quotient by x ↦ -25-x in rational affine coordinates. -/
theorem quotient_iff (x y : ℚ) :
    y^3 = quartic x ↔ (2*x^2 + 50*x + 625)^2 = (y)^3 * 4 + 78125 := by
  unfold quartic
  constructor <;> intro h <;> linarith only [h]

/-- The same quotient in the small Mordell model V² = U³ + 80. -/
theorem elliptic_iff (x y : ℚ) :
    y^3 = quartic x ↔
    ((8*x^2 + 200*x + 2500) / 125)^2 = (4*y/25)^3 + 80 := by
  unfold quartic
  constructor <;> intro h <;> linarith only [h]

/-- Two rational abscissae have the same quotient ordinate exactly when they
coincide or are paired by the deck involution. -/
theorem fibre_iff (x z : ℚ) :
    2*x^2 + 50*x + 625 = 2*z^2 + 50*z + 625 ↔ x=z ∨ z = -25-x := by
  constructor
  · intro h
    have hp : (x-z)*(25+x+z)=0 := by linarith only [h]
    rcases mul_eq_zero.mp hp with h1 | h2
    · exact Or.inl (sub_eq_zero.mp h1)
    · right; linarith
  · rintro (rfl | rfl)
    · rfl
    · ring

/-- Any positive integral witness maps to a positive affine abscissa which
is moved by the involution. -/
theorem moved_point {v s t : ℕ} (hv : 0 < v) (hs : 0 < s)
    (h : let d := 25*s^3
         5*v^4 + d*(10*v^3 + 10*v^2*d + 5*v*d^2 + d^3) = 5*t^3) :
    ∃ x y : ℚ, 0 < x ∧ y^3 = quartic x ∧ x ≠ -25-x := by
  let x := (v : ℚ) / (s : ℚ)^3
  have hx : 0 < x := by dsimp [x]; positivity
  exact ⟨x, (t : ℚ) / (s : ℚ)^4, hx, (model_iff v s t hs).mp h, by linarith⟩

end BealQuinticCubic
