import ExactInterpolation
import SubgoldenPropagation

/-! Strict growth of the true Roth number on a finite prefix, with the
upper argument rounded up. A single propagation inequality handles every
positive input in the prefix; the computation checks only four constants. -/

namespace Erdos142ShortPrefix
open Erdos142ExactInterp Erdos142Subgolden Erdos142GridInterpolation

def K : ℕ := 2662710205480735617346452022100755074809023407208374441801919604845563638678145849451440
def a₀ := 2*K-1
def b₀ := 3*K
def U : ℕ := 1673728012871958989867986830800305186225775099482896942109704653207829573676683293694064397218705807688920811454249728107076953842515517614481882245224527503990834863755235679
def V : ℕ := 2708148812749651151896932771283150653952156131579208782823480944477168028150385950107585499525882947684486814335711104976451679873802944411454434693848543550832145242581418960
def T : ℕ := 1314292663973053677518173

theorem fibonacci_constants : K = Nat.fib 420 ∧ U=K*Nat.fib 417-1 ∧ V=K*Nat.fib 418 := by
  simp only [Nat.fib_eq_fastFib]
  decide +kernel

set_option maxRecDepth 15000 in
theorem endpoints : orbit a₀ b₀ 207=(U,V) := by decide +kernel

theorem room : 2^207*a₀*T < U := by decide

theorem less_than_golden : U < V ∧ V^2 < U*V+U^2 := by decide

theorem roth_positive {n : ℕ} (hn : 0 < n) : 1 ≤ rothNumberNat n := by
  have h : ThreeAPFree (({0} : Finset ℕ) : Set ℕ) := by
    simp
  apply h.le_rothNumberNat
  · intro x hx
    simpa [Finset.mem_singleton.mp hx] using hn
  · simp

/-- Every interpolation numerator is at most its argument. -/
private theorem interp_le_input {u : ℕ} (hu : 0 < u) (x : ℕ) : interp u x ≤ x := by
  let q := x/u
  let r := x%u
  have hr : r ≤ u := (Nat.mod_lt x hu).le
  have l := Nat.mul_le_mul_left (u-r) (rothNumberNat_le q)
  have h := Nat.mul_le_mul_left r (rothNumberNat_le (q+1))
  have e : u*q+r=x := Nat.div_add_mod x u
  have sum : (u-r)*q+r*q=u*q := by rw [← Nat.add_mul,Nat.sub_add_cancel hr]
  change (u-r)*rothNumberNat q + r*rothNumberNat (q+1) ≤ x
  rw [Nat.mul_succ] at h
  omega

theorem strict_of_room (a b s u v n : ℕ) (lo : 0 < n)
    (endpoints : orbit a b s=(u,v)) (room : 2^s*a*n < u) :
    rothNumberNat n < rothNumberNat ((v*n+u-1)/u) := by
  have hu : 0 < u := (Nat.zero_le _).trans_lt room
  by_contra! flat
  have signed : (rothNumberNat ((v*n+u-1)/u):ℤ) ≤ rothNumberNat n := by exact_mod_cast flat
  have down : P u n v ≤ P u n u := by
    rw [at_den u n hu]
    exact (upper_ceil u n v hu).trans (mul_le_mul_of_nonneg_left signed (Int.natCast_nonneg u))
  have prop := propagation (P u n) (mono u n hu) (sub u n hu) (glue u n hu) a b s
  simp only [endpoints] at prop
  have penalty := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg (loss a b s)) (sub_nonpos.mpr down)
  have compress : P u n u ≤ (2:ℤ)^s*P u n a := by linarith only [prop,penalty]
  have tiny : P u n a ≤ (a*n:ℕ) := by
    unfold P
    exact_mod_cast interp_le_input hu (a*n)
  have upper := compress.trans (mul_le_mul_of_nonneg_left tiny (show 0 ≤ (2:ℤ)^s by positivity))
  have one : (1:ℤ) ≤ rothNumberNat n := by exact_mod_cast roth_positive lo
  have lower : (u:ℤ) ≤ P u n u := by
    rw [at_den u n hu]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left one (Int.natCast_nonneg u)
  have smaller : (2:ℤ)^s*↑(a*n) < (u:ℤ) := by
    exact_mod_cast (show 2^s*(a*n)<u by rwa [← Nat.mul_assoc])
  exact (not_lt_of_ge (lower.trans upper)) smaller

theorem strict_growth (n : ℕ) (lo : 0 < n) (hi : n ≤ T) :
    rothNumberNat n < rothNumberNat ((V*n+U-1)/U) :=
  strict_of_room a₀ b₀ 207 U V n lo endpoints
    ((Nat.mul_le_mul_left (2^207*a₀) hi).trans_lt room)

#print axioms fibonacci_constants
#print axioms endpoints
#print axioms less_than_golden
#print axioms strict_growth
end Erdos142ShortPrefix
