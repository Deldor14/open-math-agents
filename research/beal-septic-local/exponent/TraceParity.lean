import Mathlib.Tactic

namespace BealSeptic

/-- The parity obstruction used for completely split exponent primes. -/
theorem trace_parity {p t s : ℤ} (hp : 43 ≤ p) (hW : t^2 ≤ 36*p)
    (he : Even t) (ho : Odd s) (hs₁ : -3 ≤ s) (hs₂ : s ≤ 3) :
    ¬ p ∣ t-s := by
  have hsq : 36*p < (p-3)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ p-43 by omega) (show 0 ≤ p+1 by omega)]
  have hupper : t < p-3 := by
    by_contra! ht
    nlinarith [mul_nonneg (show 0 ≤ t-(p-3) by omega) (show 0 ≤ t+(p-3) by omega)]
  have hlower : -(p-3) < t := by
    by_contra! ht
    nlinarith [mul_nonneg (show 0 ≤ -t-(p-3) by omega) (show 0 ≤ -t+(p-3) by omega)]
  rintro ⟨k,hk⟩
  have hk₀ : k=0 := by
    rcases lt_trichotomy k 0 with h | h | h
    · have hprod := mul_nonneg (show 0≤p by omega) (show 0≤ -k-1 by omega)
      nlinarith
    · exact h
    · have hprod := mul_nonneg (show 0≤p by omega) (show 0≤k-1 by omega)
      nlinarith
  obtain ⟨x,hx⟩ := he
  obtain ⟨y,hy⟩ := ho
  rw [hk₀,mul_zero] at hk
  omega

/-- Direct count for the only completely split prime below 43. -/
theorem split_prime_29 :
    1 + ((Finset.range 29).product (Finset.range 29) |>.filter
      (fun xy : ℕ × ℕ => xy.2^2 % 29 = (xy.1^7+1) % 29)).card = 24 := by
  decide +kernel

end BealSeptic
