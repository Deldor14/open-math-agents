import OMAStatements.S_oeis_a334337
import Mathlib

open OMA.S_oeis_a334337

namespace Deldor14.TotientCube

private theorem support (n : ℕ) :
    n.factorial.totient.primeFactors ⊆ n.factorial.primeFactors := by
  intro q hq
  have prime := Nat.prime_of_mem_primeFactors hq
  have divides := Nat.dvd_of_mem_primeFactors hq
  have prod := Nat.totient_mul_prod_primeFactors n.factorial
  have both := dvd_mul_of_dvd_left divides (∏ p ∈ n.factorial.primeFactors,p)
  rw [prod] at both
  apply Nat.mem_primeFactors.mpr
  refine ⟨prime,?_,Nat.factorial_ne_zero n⟩
  rcases prime.dvd_mul.mp both with h | h
  · exact h
  · obtain ⟨p,hp,hh⟩ := ((prime.prime.dvd_finsetProd_iff (fun p : ℕ => p-1)).mp h)
    have pp := Nat.prime_of_mem_primeFactors hp
    have upper := pp.dvd_factorial.mp (Nat.dvd_of_mem_primeFactors hp)
    have lower := pp.two_le
    have le := Nat.le_of_dvd (by omega : 0 < p-1) hh
    exact prime.dvd_factorial.mpr (by omega)

private theorem stable {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y.primeFactors ⊆ x.primeFactors) : (x*y).totient = x.totient*y := by
  have same : (x*y).primeFactors=x.primeFactors := by
    rw [Nat.primeFactors_mul hx hy,Finset.union_eq_left.mpr h]
  have eq := Nat.totient_mul_prod_primeFactors (x*y)
  rw [same] at eq
  have nonzero : 0 < ∏ p ∈ x.primeFactors,p :=
    Finset.prod_pos fun p hp => Nat.pos_of_mem_primeFactors hp
  apply Nat.eq_of_mul_eq_mul_right nonzero
  calc
    _ = _ := eq
    _ = (x * ∏ p ∈ x.primeFactors,(p-1))*y := by ring
    _ = _ := by rw [← Nat.totient_mul_prod_primeFactors];ring

theorem cube (n : ℕ) (hn : 0 < n) : ∃ m : ℕ, 0 < m ∧ ∃ b : ℕ, (m*n).totient=b^3 := by
  let f := n.factorial
  let b := f.totient
  have hf : 0 < f := Nat.factorial_pos n
  have hb : 0 < b := Nat.totient_pos.mpr hf
  have div : n ∣ f := Nat.dvd_factorial hn le_rfl
  obtain ⟨k,hk⟩ := div
  have hkpos : 0 < k := by
    by_contra! h
    have kz : k=0 := by omega
    rw [kz,mul_zero] at hk
    exact hf.ne' hk
  refine ⟨k*b^2, by positivity,b,?_⟩
  rw [show k*b^2*n = f*b^2 by rw [hk]; ring,
    stable hf.ne' (pow_ne_zero _ hb.ne') (by rw [Nat.primeFactors_pow _ (by decide : 2≠0)];exact support n)]
  change b*b^2=b^3
  ring
end Deldor14.TotientCube

theorem OMA.solution : type_of% @OMA.S_oeis_a334337.main := by
  refine ⟨Deldor14.TotientCube.cube,?_⟩
  intro conjecture n hn
  obtain ⟨x,y,_,hy,eq,square,_⟩ := conjecture n 1 hn (by decide)
  refine ⟨y,hy,?_⟩
  have xy : x=y*n := by simpa [mul_comm] using eq
  rwa [← xy]
