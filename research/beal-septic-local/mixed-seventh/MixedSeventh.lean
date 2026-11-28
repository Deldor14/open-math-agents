import Mathlib.Tactic

namespace MixedSeventh

/-- Signed input for the septic descent at a fixed exponent. -/
def SignedExclusion (p : ℕ) : Prop :=
  ∀ x y z : ℤ, x.natAbs.Coprime y.natAbs → x ≠ 0 → y ≠ 0 → z ≠ 0 →
    x ^ 7 + y ^ 7 ≠ z ^ p

/-- The output base is coprime to the septic summand in a primitive solution. -/
theorem output_coprime {a b c p : ℕ} (hab : a.Coprime b)
    (h : a ^ 7 + b ^ p = c ^ 7) : c.Coprime a := by
  by_contra hn
  obtain ⟨l, hl, hlc, hla⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  have hsum : l ∣ a ^ 7 + b ^ p := h ▸ (hlc.trans (dvd_pow_self c (by decide)))
  have hlb : l ∣ b := hl.dvd_of_dvd_pow ((Nat.dvd_add_iff_right
    (hla.trans (dvd_pow_self a (by decide : 7 ≠ 0)))).mpr hsum)
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨l, hl, hla, hlb⟩) hab

/-- Apply a signed exclusion to the mixed leaf, including exponent multiples. -/
theorem mixed_multiples {p a b c i j r : ℕ}
    (hs : SignedExclusion p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a.Coprime b) (hi : 7 ∣ i) (hj : p ∣ j) (hr : 7 ∣ r) :
    a ^ i + b ^ j ≠ c ^ r := by
  obtain ⟨u, rfl⟩ := hi
  obtain ⟨v, rfl⟩ := hj
  obtain ⟨w, rfl⟩ := hr
  intro eqn
  rw [Nat.mul_comm 7 u, Nat.mul_comm p v, Nat.mul_comm 7 w,
      pow_mul, pow_mul, pow_mul] at eqn
  have cop := output_coprime ((hab.pow_left u).pow_right v) eqn
  let x : ℤ := (c ^ w : ℕ)
  let y : ℤ := -((a ^ u : ℕ) : ℤ)
  let z : ℤ := (b ^ v : ℕ)
  have co : x.natAbs.Coprime y.natAbs := by simpa [x, y] using cop
  have hx : x ≠ 0 := by dsimp [x]; positivity
  have hy : y ≠ 0 := by dsimp [y]; simp [ha.ne']
  have hz : z ≠ 0 := by dsimp [z]; positivity
  apply hs x y z co hx hy hz
  have liftEq : ((a ^ u : ℕ) : ℤ) ^ 7 + ((b ^ v : ℕ) : ℤ) ^ p =
      ((c ^ w : ℕ) : ℤ) ^ 7 := by exact_mod_cast eqn
  change ((c ^ w : ℕ) : ℤ) ^ 7 + (-((a ^ u : ℕ) : ℤ)) ^ 7 = ((b ^ v : ℕ) : ℤ) ^ p
  linear_combination -liftEq

/-- Archimedean contradiction for a difference, when every prime of the larger
base has been absorbed in the cyclotomic congruence. -/
theorem difference_growth (p v : ℕ) (hp : 31 ≤ p) (hv : 3 ≤ v) :
    7 * (2*p)^6 < v^(p-6) := by
  have step (n : ℕ) (hn : 7 ≤ n) : 7*(2*(n+1))^6 ≤ 3*(7*(2*n)^6) := by
    have b : 7*(n+1) ≤ 8*n := by omega
    have b' := Nat.pow_le_pow_left b 6
    norm_num [mul_pow] at b' ⊢
    omega
  have grow (k : ℕ) : 7*(2*(31+k))^6 < 3^(25+k) := by
    induction k with
    | zero => decide
    | succ k ih =>
      have up := step (31+k) (by omega)
      rw [show 25+k.succ=(25+k)+1 by omega, pow_succ]
      change 7*(2*((31+k)+1))^6 < _
      omega
  have bound := grow (p-31)
  rw [show 31+(p-31)=p by omega, show 25+(p-31)=p-6 by omega] at bound
  exact bound.trans_le (Nat.pow_le_pow_left hv (p-6))

end MixedSeventh
