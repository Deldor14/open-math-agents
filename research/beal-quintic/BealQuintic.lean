import Mathlib

/-!
# Signed quintic cofactor and its rational quotient

This file treats the two quintic cofactor leaves of Left to Solve and the
corresponding two branches with arbitrary output exponent. Poonen gives the
elliptic quotient for exponent three in Acta Arith. 86, section 4.
-/

namespace BealQuintic

def cofactor (a b : ℚ) : ℚ := a^4-a^3*b+a^2*b^2-a*b^3+b^4

def angle (a b : ℚ) : ℚ := (a^2+b^2)/(a+b)^2

theorem split (a b : ℚ) : a^5+b^5=(a+b)*cofactor a b := by
  unfold cofactor
  ring

theorem normalized (a b : ℚ) (hd : a+b≠0) :
    5*(angle a b)^2 = 1+4*cofactor a b/(a+b)^4 ∧
    2*angle a b-1=((a-b)/(a+b))^2 := by
  unfold angle cofactor
  constructor <;> field_simp [hd] <;> ring

theorem difference_cofactor (v d : ℚ) : cofactor (v+d) (-v) =
    5*v^4+d*(10*v^3+10*v^2*d+5*v*d^2+d^3) := by
  unfold cofactor
  ring

/-- Handles either sign for b, and arbitrary natural output exponent. -/
theorem general_branch (a b t s k : ℚ) (r : ℕ) (hd : a+b≠0) (hs : s≠0)
    (hscale : k*(a+b)=s^r) (hq : cofactor a b=k*t^r) :
    5*(angle a b)^2=1+4*k^5*(t/s^4)^r ∧
    2*angle a b-1=((a-b)/(a+b))^2 := by
  obtain ⟨h₁,h₂⟩ := normalized a b hd
  refine ⟨?_,h₂⟩
  rw [h₁, hq, div_pow, ← pow_mul, Nat.mul_comm 4 r, pow_mul, ← hscale]
  have hk : k ≠ 0 := by
    intro hh
    rw [hh, zero_mul] at hscale
    exact pow_ne_zero r hs hscale.symm
  field_simp [hd, hk]

/-- Reconstruct both normalized summands; their sum is exactly one. -/
theorem rational_lift (U W T k : ℚ) (r : ℕ)
    (hcover : 2*U-1=W^2) (hcurve : 5*U^2=1+4*k^5*T^r) :
    let a := (1+W)/2
    let b := (1-W)/2
    a+b=1 ∧ angle a b=U ∧ cofactor a b=k^5*T^r := by
  dsimp
  have hd : (1+W)/2+(1-W)/2=1 := by ring
  have hU : U=(W^2+1)/2 := by linarith
  have ha : angle ((1+W)/2) ((1-W)/2)=U := by
    unfold angle
    rw [hd,hU]
    ring
  have hn := (normalized ((1+W)/2) ((1-W)/2) (by rw [hd]; norm_num)).1
  rw [ha,hd] at hn
  norm_num at hn
  exact ⟨hd, ha, by linarith⟩

/-- The two rational cube leaves, with the extra rational square condition
needed to lift a point on the elliptic quotient. -/
theorem first_cubic_iff (X Y : ℚ) :
    (Y^2=X^3+2000 ∧ ∃ W : ℚ, Y/50-1=W^2) ↔
    ∃ W : ℚ, cofactor ((1+W)/2) ((1-W)/2)=(X/20)^3 ∧ Y=50*(W^2+1) := by
  constructor
  · rintro ⟨hE,W,hW⟩
    have h := rational_lift (Y/100) W (X/20) 1 3 (by linarith) (by norm_num; linarith)
    norm_num at h
    exact ⟨W,h.2.2,by linarith⟩
  · rintro ⟨W,hQ,rfl⟩
    unfold cofactor at hQ
    constructor
    · linear_combination 8000*hQ
    · exact ⟨W, by ring⟩

theorem second_cubic_iff (X Y : ℚ) :
    (Y^2=X^3+80 ∧ ∃ W : ℚ, Y/10-1=W^2) ↔
    ∃ W : ℚ, cofactor ((1+W)/2) ((1-W)/2)=(X/4)^3/5 ∧ Y=10*(W^2+1) := by
  constructor
  · rintro ⟨hE,W,hW⟩
    have h := rational_lift (Y/20) W (X/100) 5 3 (by linarith) (by norm_num; linarith)
    norm_num at h
    refine ⟨W,?_,by linarith⟩
    rw [h.2.2]
    ring
  · rintro ⟨W,hQ,rfl⟩
    unfold cofactor at hQ
    constructor
    · linear_combination 320*hQ
    · exact ⟨W, by ring⟩

#print axioms difference_cofactor
#print axioms general_branch
#print axioms rational_lift
#print axioms first_cubic_iff
#print axioms second_cubic_iff

end BealQuintic
