import OMAStatements.S_oeis_a001917
import Mathlib

/-! The Wieferich prime 1093 gives a counterexample at its square.
The order of two modulo 1093² divides 364, so the single summand for
the full modulus already exceeds twice the largest possible primeTerm. -/
namespace Deldor14.DoublingCosets
open OMA.S_oeis_a001917 Finset
theorem result : ¬(type_of% @OMA.S_oeis_a001917.main) := by
  have hp : Nat.Prime 1093 := by norm_num
  let m : ℕ := 1093^2
  have power : (2:ZMod m)^364=1 := by decide +kernel
  have od := orderOf_dvd_of_pow_eq_one power
  have pos : 0<orderOf (2:ZMod m) := Nat.pos_of_dvd_of_pos od (by decide)
  have upper : orderOf (2:ZMod m)≤364 := Nat.le_of_dvd (by decide) od
  have phi : m.totient=1093*1092 := Nat.totient_prime_pow_succ hp 1
  have ratio : 3279 ≤ m.totient/orderOf (2:ZMod m) := by
    rw [Nat.le_div_iff_mul_le pos,phi]
    omega
  have mem : m ∈ m.divisors.filter (fun d => 1<d) := by
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_refl _,by decide⟩,by decide⟩
  have bigger : 3279≤cosets m := ratio.trans (single_le_sum
    (f:=fun d => d.totient / orderOf (2:ZMod d)) (fun _ _ => Nat.zero_le _) mem)
  have smaller : primeTerm 1093 ≤ 1092 := Nat.div_le_self _ _
  intro h
  have eq := h 1093 2 hp (by decide) (by decide)
  change 2*primeTerm 1093=cosets m at eq
  omega
end Deldor14.DoublingCosets
theorem OMA.disproof : ¬(type_of% @OMA.S_oeis_a001917.main) := Deldor14.DoublingCosets.result
