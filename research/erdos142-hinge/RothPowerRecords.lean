import RothFutureRecords
import RothHeight

namespace Erdos142FutureRecords
open Finset

/-- Comparison at a rational exponent a/b using integer arithmetic. -/
def PowerLE (a b i j : ℕ) := j^a*(rothNumberNat i)^b ≤ i^a*(rothNumberNat j)^b

private theorem power_trans {a b i j k : ℕ} (hj : 0<j)
    (hij : PowerLE a b i j) (hjk : PowerLE a b j k) : PowerLE a b i k := by
  unfold PowerLE at *
  have x := Nat.mul_le_mul_left (k^a) hij
  have y := Nat.mul_le_mul_left (i^a) hjk
  have cap : j^a*(k^a*(rothNumberNat i)^b) ≤ j^a*(i^a*(rothNumberNat k)^b) := by
    nlinarith only [x,y]
  exact Nat.le_of_mul_le_mul_left cap (pow_pos hj a)

/-- Given a progression-free digit template certificate, checking an
    unbounded future inequality at exponent a/b needs only one finite interval. -/
theorem power_test (a b s n : ℕ) (hs : 0<s) (ns : 2*s≤n)
    (cert : (2*s+1)^a≤(rothNumberNat s)^b) :
    (∀ m≥n, PowerLE a b n m) ↔ ∀ m ∈ Ico n (2*s*n), PowerLE a b n m := by
  constructor
  · intro h m hm
    exact h _ (mem_Ico.mp hm).1
  · intro h m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro nm
      by_cases stop : m<2*s*n
      · exact h _ (mem_Ico.mpr ⟨nm,stop⟩)
      · let k := m/(2*s)
        have den : 0<2*s := by omega
        have nk : n≤k := (Nat.le_div_iff_mul_le den).mpr (by rw [Nat.mul_comm]; omega)
        have kp : 0<k := by omega
        have small : k<m := Nat.div_lt_self (by omega) (by omega)
        have out := ih k small nk
        have mod := Nat.mod_add_div m (2*s)
        have rem := Nat.mod_lt m den
        have size : m≤(2*s+1)*k := by rw [Nat.add_mul,Nat.one_mul]; dsimp [k] at *; omega
        have inc : 2*s*k≤m := by dsimp [k]; omega
        have digit := (Erdos142Height.digit_product s k).trans (rothNumberNat.monotone inc)
        have x := Nat.pow_le_pow_left size a
        rw [mul_pow] at x
        have y := Nat.pow_le_pow_left digit b
        rw [mul_pow] at y
        have cr := Nat.mul_le_mul_right (k^a) cert
        apply power_trans kp out
        unfold PowerLE
        calc
          m^a*(rothNumberNat k)^b ≤ ((rothNumberNat s)^b*k^a)*(rothNumberNat k)^b :=
            Nat.mul_le_mul_right _ (x.trans cr)
          _ = k^a*((rothNumberNat s)^b*(rothNumberNat k)^b) := by ring
          _ ≤ k^a*(rothNumberNat m)^b := Nat.mul_le_mul_left _ y

/-- The square-root test is also entirely integer-valued. -/
theorem square_iff {n m : ℕ} (np : 0<n) (mp : 0<m) :
    score n ≤ score m ↔ PowerLE 1 2 n m := by
  have pn : 0<Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast np)
  have pm : 0<Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast mp)
  dsimp only [score,PowerLE]
  rw [div_le_div_iff₀ pn pm,pow_one,pow_one]
  have l : 0≤(rothNumberNat n:ℝ)*Real.sqrt m := by positivity
  have r : 0≤(rothNumberNat m:ℝ)*Real.sqrt n := by positivity
  rw [← sq_le_sq₀ l r, mul_pow,mul_pow,Real.sq_sqrt (show 0≤(m:ℝ) by positivity),
    Real.sq_sqrt (show 0≤(n:ℝ) by positivity)]
  exact_mod_cast (show (rothNumberNat n)^2*m≤(rothNumberNat m)^2*n ↔
    m*(rothNumberNat n)^2≤n*(rothNumberNat m)^2 by rw [Nat.mul_comm m,Nat.mul_comm n])

#print axioms power_test
#print axioms square_iff
end Erdos142FutureRecords
