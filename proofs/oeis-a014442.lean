import OMAStatements.S_oeis_a014442
import Mathlib

/-! A nonzero residue x with x² = -1 admits a representative n < p.
Factoring n²+1 as p times a cofactor less than p bounds every prime factor. -/
namespace Deldor14.LargestPrimeQuadratic
theorem full : type_of% @OMA.S_oeis_a014442.main := by
  intro p hp h4
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,hx⟩ := (ZMod.exists_sq_eq_neg_one_iff (p:=p)).mpr (by omega)
  let n:=x.val
  have bound : n<p := x.val_lt
  have hdiv : p ∣ n^2+1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    simpa [n,pow_two,←hx] using (neg_add_cancel (1 : ZMod p))
  obtain ⟨d,hd⟩ := hdiv
  have hn : 0<n := by
    by_contra! h
    have : n=0 := by omega
    have hdvd : p ∣ 1 := by simpa [this] using (show p ∣ n^2+1 from ⟨d,hd⟩)
    exact hp.not_dvd_one hdvd
  have dpos : 0<d := by
    by_contra! hh
    have dz : d=0 := Nat.eq_zero_of_le_zero hh
    rw [dz,mul_zero] at hd
    omega
  have small : d≤p := by
    by_contra! e
    nlinarith [Nat.mul_le_mul (show n+1≤p by omega) (show n+1≤d by omega)]
  refine ⟨n,hn,⟨d,hd⟩,?_⟩
  intro q hq
  have pq := Nat.prime_of_mem_primeFactors hq
  have dt := Nat.dvd_of_mem_primeFactors hq
  rw [hd] at dt
  rcases pq.dvd_mul.mp dt with h | h
  · exact Nat.le_of_dvd hp.pos h
  · exact (Nat.le_of_dvd dpos h).trans small
end Deldor14.LargestPrimeQuadratic
theorem OMA.solution : type_of% @OMA.S_oeis_a014442.main := Deldor14.LargestPrimeQuadratic.full
