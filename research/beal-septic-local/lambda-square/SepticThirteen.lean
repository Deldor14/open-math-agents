import Mathlib.Tactic

namespace SepticThirteen

/-- The second curve uses all three conjugate linear factors. -/
theorem triple_identity {R : Type*} [CommRing R] (s d₁ d₂ d₃ t : R)
    (h : t * (d₂-d₁) = d₂-d₃) :
    t*(1-d₁*s)-(1-d₃*s) = (t-1)*(1-d₂*s) := by
  linear_combination s*h

/-- For the twelve nonzero residues and k = 1,2, the power 12-k is the inverse k-th power. -/
def finiteLog (k t : ℕ) : ZMod 13 :=
  (Finset.range 12).sum fun j => (t : ZMod 13)^(j+1) * ((j+1 : ℕ) : ZMod 13)^(12-k)

/-- The local witness at theta = 7, T = 141 mod 169. -/
theorem dilog_witness :
    finiteLog 1 11=8 ∧ finiteLog 2 11=10 ∧
    (2*finiteLog 2 11-2*finiteLog 1 11 : ZMod 13)=4 := by decide +kernel

theorem unit_minor : (2*12-1*5 : ZMod 13)=6 := by decide +kernel

end SepticThirteen
