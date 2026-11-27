import OMAStatements.S_oeis_a057192
import Mathlib

/-! Sierpiński's classical covering for the prime 271129 refutes the
OEIS parity conjecture when the sequence uses the prescribed value -1.
See Baillie, Cormack and Williams, Math. Comp. 37 (1981), p. 229,
and Jianing Song's correction in OEIS A057192 (December 2021). -/
namespace Deldor14.Sierpinski
open OMA.S_oeis_a057192
private theorem no_exponent (m : ℕ) : ¬(1+271129*2^m).Prime := by
  let r : Fin 24 := ⟨m%24,Nat.mod_lt _ (by decide)⟩
  have cover : ∀ i : Fin 24, ∃ w : Fin 242, 2≤w.val ∧ 2^24%w.val=1 ∧
    (1+271129*2^i.val)%w.val=0 := by decide +kernel
  obtain ⟨w,lo,period,zero⟩ := cover r
  have base : (2:ℕ)^24 ≡ 1 [MOD w.val] := by
    change 2^24%w.val=1%w.val
    rwa [Nat.mod_eq_of_lt (by omega : 1<w.val)]
  have step := base.pow (m/24)
  rw [one_pow,←pow_mul] at step
  have e := (Nat.ModEq.refl (2^r.val)).mul step
  rw [mul_one,←pow_add] at e
  have dec : r.val+24*(m/24)=m := Nat.mod_add_div m 24
  rw [dec] at e
  have e' := (Nat.ModEq.refl 1).add ((Nat.ModEq.refl 271129).mul e)
  change (1+271129*2^m)%w.val=(1+271129*2^r.val)%w.val at e'
  have hd : w.val ∣ 1+271129*2^m := Nat.dvd_iff_mod_eq_zero.mpr (e'.trans zero)
  intro prime
  have self := (Nat.dvd_prime_two_le prime lo).mp hd
  have low : 1 ≤ (2:ℕ)^m := Nat.one_le_pow _ _ (by decide)
  have high := w.isLt
  omega

theorem result : ¬(type_of% @OMA.S_oeis_a057192.main) := by
  classical
  let k := Nat.count Nat.Prime 271129
  have hp : Nat.Prime 271129 := by norm_num
  have nth : Nat.nth Nat.Prime k=271129 := Nat.nth_count hp
  have pos : 0<k := by
    by_contra! h
    have z : k=0 := by omega
    rw [z,Nat.nth_prime_zero_eq_two] at nth
    exact (by decide : (2:ℕ)≠271129) nth
  intro h
  have ev := (h (k+1) (by omega)).mpr (by simpa [nth] using (show 271129%3=1 by decide))
  have none : ¬ ∃ m : ℕ, (1+Nat.nth Nat.Prime (k+1-1)*2^m).Prime := by
    simpa only [Nat.add_sub_cancel,nth,not_exists] using no_exponent
  rw [a,dif_neg none] at ev
  exact (by decide : ¬Even (-1:ℤ)) ev
end Deldor14.Sierpinski
theorem OMA.disproof : ¬(type_of% @OMA.S_oeis_a057192.main) := Deldor14.Sierpinski.result
