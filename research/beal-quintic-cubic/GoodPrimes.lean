import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

namespace BealGoodPrimes

/-- The algebra with coordinates a + b√d over the prime field. -/
abbrev Ext (p : ℕ) (d : ZMod p) := QuadraticAlgebra (ZMod p) d 0

def elements (p : ℕ) (d : ZMod p) : List (Ext p d) :=
  (List.finRange p).flatMap fun i =>
    (List.finRange p).map fun j => ⟨(i.val : ZMod p), (j.val : ZMod p)⟩

def f {R : Type*} [CommRing R] (x : R) : R :=
  (((x + 50)*x + 1250)*x + 15625)*x + 78125

/-- Count ordered affine solutions directly by the multiplicity of each value
of the cube map. The one additional point is the unique point at infinity. -/
def projectiveCount (p : ℕ) [NeZero p] (d : ZMod p) : ℕ :=
  let elts := elements p d
  let cubes := elts.map (fun y => y^3)
  1 + ((elts.map f).map fun v => cubes.count v).sum

theorem irreducible_parameter_11 : ∀ a : ZMod 11, a^2 ≠ 2 := by decide +kernel
theorem irreducible_parameter_17 : ∀ a : ZMod 17, a^2 ≠ 3 := by decide +kernel

/-- Setting Z=0 in the homogenized quartic forces X=0. -/
theorem at_infinity {K : Type*} [Field K] (X Y : K) :
    Y^3*(0 : K) = X^4 + 50*X^3*0 + 1250*X^2*0^2 +
        15625*X*0^3 + 78125*0^4 ↔ X=0 := by simp [eq_comm (a := (0 : K))]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 20000000 in
theorem count_11_sq : projectiveCount 11 2 = 152 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 40000000 in
theorem count_17_sq : projectiveCount 17 3 = 376 := by decide +kernel

/-- Arithmetic consequence once the specialization maps give both divisibilities. -/
theorem torsion_order_bound (n : ℕ) (h11 : n ∣ 126) (h17 : n ∣ 316) : n ∣ 2 := by
  exact Nat.dvd_gcd h11 h17


set_option maxRecDepth 40000 in
set_option maxHeartbeats 40000000 in
theorem enumeration_11 : ∀ i j : ZMod 11,
    (elements 11 2).count ⟨i,j⟩ = 1 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 40000000 in
theorem enumeration_17 : ∀ i j : ZMod 17,
    (elements 17 3).count ⟨i,j⟩ = 1 := by decide +kernel

/-- Evaluate the genus-three reciprocal Weil polynomial at 1 from the first
three curve counts, by the Newton identities. -/
def orderFromCounts (p n₁ n₂ n₃ : ℤ) : ℤ :=
  let t₁ := p+1-n₁
  let t₂ := p^2+1-n₂
  let t₃ := p^3+1-n₃
  let e₂ := (t₁^2-t₂)/2
  let e₃ := (t₁^3-3*t₁*t₂+2*t₃)/6
  p^3+1-(p^2+1)*t₁+(p+1)*e₂-e₃

theorem orders_11 :
    orderFromCounts 11 12 (projectiveCount 11 2) 1332 = 12 * 126 := by
  rw [count_11_sq]
  decide

theorem orders_17 :
    orderFromCounts 17 18 (projectiveCount 17 3) 4914 = 18 * 316 := by
  rw [count_17_sq]
  decide

end BealGoodPrimes
