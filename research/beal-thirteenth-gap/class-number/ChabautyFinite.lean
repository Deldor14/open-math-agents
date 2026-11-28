import Mathlib

namespace BealThirteenth.Seven

/-- Coefficients of A*B over Z/25Z, indexed in increasing degree. -/
def mulCoeff (A B : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((List.range (n+1)).map (fun i => A i * B (n-i))).sum % 25

def coeff (A : List ℕ) (n : ℕ) : ℕ := A[n]?.getD 0

def h := coeff [15,20,20,6,1]
def g := coeff [15,5,20,21,0,17,21,14]
def f (n : ℕ) : ℕ :=
  if n = 0 then 36 else Nat.choose 7 n * 7^(7-n)

/-- The norm of g+h*y records the abscissas of the residual degree-three divisor. -/
theorem residualPolynomial (n : Fin 16) :
    (mulCoeff (mulCoeff h h) f n + 25 - mulCoeff g g n) % 25 =
      coeff [0,0,0,0,0,0,0,0,0,0,0,0,15,5,15,1] n := by
  revert n
  decide

/-- The two finite residue classes allowed by the descent at 5. -/
theorem finiteDisks (x y : ZMod 5) (heq : y^2 = x^7 + 3)
    (hsq : ∃ t : ZMod 5, t^2 = if x = 3 then 7*3^6 else x-3) :
    x = 2 ∧ (y = 1 ∨ y = 4) := by
  revert hsq heq y x
  decide

end BealThirteenth.Seven
