import OMAStatements.S_oeis_a025527
import Mathlib

/-! Both the factorial and lcm have exactly the primes up to m as prime
divisors. Euler's product formula gives the same totient quotient for all m. -/
namespace Deldor14.TotientLcm
open Nat Finset OMA.S_oeis_a025527
theorem all_m (m : ℕ) : m.factorial/L m=m.factorial.totient/(L m).totient := by
  have dv : L m ∣ m.factorial := Finset.lcm_dvd (fun i hi => Nat.dvd_factorial (mem_Icc.mp hi).1 (mem_Icc.mp hi).2)
  have nz : L m ≠ 0 := fun h => (Nat.factorial_ne_zero m) (by simpa [h] using dv)
  have eq : (L m).primeFactors=m.factorial.primeFactors := by
    ext p
    rw [Nat.mem_primeFactors_of_ne_zero nz,Nat.mem_primeFactors_of_ne_zero (factorial_ne_zero m)]
    constructor
    · exact fun ⟨hp,hd⟩ => ⟨hp,hd.trans dv⟩
    · rintro ⟨hp,hd⟩
      exact ⟨hp, Finset.dvd_lcm (f:=id) (mem_Icc.mpr ⟨hp.pos,hp.dvd_factorial.mp hd⟩)⟩
  obtain ⟨k,hk⟩ := dv
  have a := Nat.totient_mul_prod_primeFactors m.factorial
  have b := Nat.totient_mul_prod_primeFactors (L m)
  rw [eq] at b
  have pos : 0 < ∏ p ∈ m.factorial.primeFactors,p :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have e : m.factorial.totient=(L m).totient*k := by
    apply Nat.eq_of_mul_eq_mul_right pos
    calc
      _ = m.factorial * ∏ p ∈ m.factorial.primeFactors, (p-1) := a
      _ = k*(L m * ∏ p ∈ m.factorial.primeFactors, (p-1)) := by nth_rw 1 [hk];ring
      _ = _ := by rw [←b];ring
  have tl := Nat.totient_pos.mpr (Nat.pos_of_ne_zero nz)
  rw [e,hk,Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero nz),Nat.mul_div_cancel_left _ tl]
end Deldor14.TotientLcm
theorem OMA.solution : type_of% @OMA.S_oeis_a025527.main := fun p _ => Deldor14.TotientLcm.all_m (p-1)
