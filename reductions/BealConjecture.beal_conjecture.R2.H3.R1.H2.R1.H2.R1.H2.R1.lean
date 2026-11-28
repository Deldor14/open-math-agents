import OMAReductions.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1_H2_R1
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

-- Credit: @Deldor14
-- Continue the m = 25 quartic step of @Hennyrick. Work in the basis 1,φ
-- with φ² = φ + 1. The two coefficients of (a+bφ)^3 are P and Q below.

namespace OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1_H2_R1_H2_R1

/-- Primitive norm cubes in the golden integer ring are cubes up to a unit
represented by 1, φ, or φ². The condition on B controls the ramified prime. -/
def H1 : Prop :=
  ∀ A B t : ℕ, A.Coprime B → 5 ∣ B →
    (A : ℤ)^2 + (A : ℤ)*B - (B : ℤ)^2 = (t : ℤ)^3 →
    ∃ a b : ℤ,
      let P := a^3 + 3*a*b^2 + b^3
      let Q := 3*a^2*b + 3*a*b^2 + 2*b^3
      ((A : ℤ) = P ∧ (B : ℤ) = Q) ∨
      ((A : ℤ) = Q ∧ (B : ℤ) = P+Q) ∨
      ((A : ℤ) = P+Q ∧ (B : ℤ) = P+2*Q)

/-- On the untwisted cubic, exclude a square whose positive root exceeds 25. -/
def H2 : Prop :=
  ∀ a b w : ℚ, 25 < w → 3*a^2*b + 3*a*b^2 + 2*b^3 = 125 →
    w^2 ≠ 4*(a^3 + 3*a*b^2 + b^3) - 375

/-- The corresponding square exclusion on the cubic twisted by φ. -/
def H3 : Prop :=
  ∀ a b w : ℚ, 25 < w → a^3 + 3*a^2*b + 6*a*b^2 + 3*b^3 = 125 →
    w^2 ≠ 4*(3*a^2*b + 3*a*b^2 + 2*b^3) - 375

theorem primitive_coefficients (v s : ℕ) (hc : (25*s^3).Coprime v) :
    (v^2 + 25*v*s^3 + 250*s^6).Coprime (125*s^6) := by
  have h5 : (5 : ℕ).Coprime v := Nat.Coprime.coprime_dvd_left
    (show 5 ∣ 25*s^3 from ⟨5*s^3, by ring⟩) hc
  have hs : s.Coprime v := Nat.Coprime.coprime_dvd_left
    (show s ∣ 25*s^3 from ⟨25*s^2, by ring⟩) hc
  have hc5 : (5 : ℕ).Coprime (v^2+25*v*s^3+250*s^6) := by
    change Nat.gcd 5 _ = 1
    rw [show v^2+25*v*s^3+250*s^6 = v^2+5*(5*v*s^3+50*s^6) by ring,
      Nat.gcd_add_mul_left_right]
    exact h5.pow_right 2
  have hcs : s.Coprime (v^2+25*v*s^3+250*s^6) := by
    change Nat.gcd s _ = 1
    rw [show v^2+25*v*s^3+250*s^6 = v^2+s*(25*v*s^2+250*s^5) by ring,
      Nat.gcd_add_mul_left_right]
    exact hs.pow_right 2
  exact (hc5.symm.pow_right 3).mul_right (hcs.symm.pow_right 6)

theorem last_twist_impossible (v s : ℕ) (a b : ℤ) (hc : (25*s^3).Coprime v)
    (hA : (v : ℤ)^2+25*v*(s : ℤ)^3+250*(s : ℤ)^6 =
      (a^3+3*a*b^2+b^3)+(3*a^2*b+3*a*b^2+2*b^3))
    (hB : 125*(s : ℤ)^6 = (a^3+3*a*b^2+b^3)+2*(3*a^2*b+3*a*b^2+2*b^3)) :
    False := by
  have table : ∀ v s a b : ZMod 2, ¬(v = 0 ∧ s = 0) →
      ¬(v^2+25*v*s^3+250*s^6 = (a^3+3*a*b^2+b^3)+(3*a^2*b+3*a*b^2+2*b^3) ∧
        125*s^6 = (a^3+3*a*b^2+b^3)+2*(3*a^2*b+3*a*b^2+2*b^3)) := by decide +kernel
  have ha := congrArg (fun z : ℤ => (z : ZMod 2)) hA
  have hb := congrArg (fun z : ℤ => (z : ZMod 2)) hB
  push_cast at ha hb
  have hp : ¬ ((v : ZMod 2) = 0 ∧ (s : ZMod 2) = 0) := by
    rintro ⟨hv,hs⟩
    have hvs := (ZMod.natCast_eq_zero_iff v 2).mp hv
    have hss := (ZMod.natCast_eq_zero_iff s 2).mp hs
    have hd := Nat.dvd_gcd (hss.trans (show s ∣ 25*s^3 from ⟨25*s^2, by ring⟩)) hvs
    rw [hc.gcd_eq_one] at hd
    exact (by decide : ¬ 2 ∣ 1) hd
  exact table v s a b hp ⟨ha,hb⟩

theorem main : H1 → H2 → H3 → OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1_H2_R1.H2 := by
  intro hnorm hplain htwist v s t hv hs _ hc _ _
  dsimp only
  intro he
  let A := v^2+25*v*s^3+250*s^6
  let B := 125*s^6
  have heZ : 5*(v : ℤ)^4 + (25*(s : ℤ)^3) * (10*(v : ℤ)^3 +
      10*(v : ℤ)^2*(25*(s : ℤ)^3) + 5*(v : ℤ)*(25*(s : ℤ)^3)^2 +
      (25*(s : ℤ)^3)^3) = 5*(t : ℤ)^3 := by exact_mod_cast he
  have hn : (A : ℤ)^2 + (A : ℤ)*B - (B : ℤ)^2 = (t : ℤ)^3 := by
    dsimp [A,B]
    linarith only [heZ]
  obtain ⟨a,b,hab⟩ := hnorm A B t (primitive_coefficients v s hc) ⟨25*s^6,by dsimp [B];ring⟩ hn
  let S : ℚ := s
  let V : ℚ := v
  let W := (2*V+25*S^3)/S^3
  have hS : S ≠ 0 := by dsimp [S]; positivity
  have hW : 25 < W := by
    dsimp [W]
    apply (lt_div_iff₀ (by dsimp [S]; positivity : 0 < S^3)).2
    have hV : 0 < V := by dsimp [V]; positivity
    linarith
  rcases hab with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have hA : V^2+25*V*S^3+250*S^6 = (a : ℚ)^3 + 3*a*(b : ℚ)^2 + (b : ℚ)^3 := by
      dsimp [V,S]
      have hr := congrArg (fun z : ℤ => (z : ℚ)) ha
      dsimp [A] at hr
      push_cast at hr
      exact hr
    have hB : 125*S^6 = 3*(a : ℚ)^2*b+3*a*(b : ℚ)^2+2*(b : ℚ)^3 := by
      dsimp [S]
      have hr := congrArg (fun z : ℤ => (z : ℚ)) hb
      dsimp [B] at hr
      push_cast at hr
      exact hr
    apply hplain ((a : ℚ)/S^2) ((b : ℚ)/S^2) W hW
    · field_simp [hS]; linarith only [hB]
    · dsimp [W]; field_simp [hS]; linarith only [hA]
  · have hA : V^2+25*V*S^3+250*S^6 = 3*(a : ℚ)^2*b+3*a*(b : ℚ)^2+2*(b : ℚ)^3 := by
      dsimp [V,S]
      have hr := congrArg (fun z : ℤ => (z : ℚ)) ha
      dsimp [A] at hr
      push_cast at hr
      exact hr
    have hB : 125*S^6 = ((a : ℚ)^3+3*a*(b : ℚ)^2+(b : ℚ)^3)+
        (3*(a : ℚ)^2*b+3*a*(b : ℚ)^2+2*(b : ℚ)^3) := by
      dsimp [S]
      have hr := congrArg (fun z : ℤ => (z : ℚ)) hb
      dsimp [B] at hr
      push_cast at hr
      exact hr
    apply htwist ((a : ℚ)/S^2) ((b : ℚ)/S^2) W hW
    · field_simp [hS]; linarith only [hB]
    · dsimp [W]; field_simp [hS]; linarith only [hA]
  · apply last_twist_impossible v s a b hc
    · dsimp [A] at ha; exact ha
    · dsimp [B] at hb; exact hb

end OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1_H2_R1_H2_R1
