import OMAStatements.S_oeis_a088276
import Mathlib

/-! The suffix 162207 is divisible by three and satisfies the entry's
admissibility conditions. The primes 11, 101, 73 and 137 cover the eight
exponent classes modulo 8 of 10^k + 162207. -/
namespace Deldor14.DecimalSuffix
open OMA.S_oeis_a088276
private theorem no_exponent (m : ℕ) : ¬(10^m+162207).Prime := by
  let r : Fin 8 := ⟨m%8,Nat.mod_lt _ (by decide)⟩
  have cover : ∀ i : Fin 8, ∃ w : Fin 138, 2≤w.val ∧ 10^8%w.val=1 ∧
    (10^i.val+162207)%w.val=0 := by decide +kernel
  obtain ⟨w,lo,period,zero⟩ := cover r
  have base : (10:ℕ)^8 ≡ 1 [MOD w.val] := by
    change 10^8%w.val=1%w.val
    rwa [Nat.mod_eq_of_lt (by omega : 1<w.val)]
  have step := base.pow (m/8)
  rw [one_pow,←pow_mul] at step
  have e := (Nat.ModEq.refl (10^r.val)).mul step
  rw [mul_one,←pow_add] at e
  have dec : r.val+8*(m/8)=m := Nat.mod_add_div m 8
  rw [dec] at e
  have e' := e.add (Nat.ModEq.refl 162207)
  change (10^m+162207)%w.val=(10^r.val+162207)%w.val at e'
  have hd : w.val ∣ 10^m+162207 := Nat.dvd_iff_mod_eq_zero.mpr (e'.trans zero)
  intro prime
  have self := (Nat.dvd_prime_two_le prime lo).mp hd
  have low : 1 ≤ (10:ℕ)^m := Nat.one_le_pow _ _ (by decide)
  have high := w.isLt
  omega

theorem result : ¬(type_of% @OMA.S_oeis_a088276.main) := by
  classical
  intro h
  have adm : allowed 162207 := ⟨by decide,⟨81103,by decide⟩,by decide⟩
  have empty : {k : ℕ | Nat.Prime (10^k+162207)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    exact no_exponent
  have inf := h.2 162207 adm (by decide)
  rw [empty] at inf
  exact inf Set.finite_empty
end Deldor14.DecimalSuffix
theorem OMA.disproof : ¬(type_of% @OMA.S_oeis_a088276.main) := Deldor14.DecimalSuffix.result
