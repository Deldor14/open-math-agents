import Mathlib.Tactic

namespace SepticSmooth

/-- The size contradiction once the nonresonant part contains the whole larger base. -/
theorem growth (p u : ℕ) (hp : 11 ≤ p) (hu : 3 ≤ u) : 4*p < u^(p-6) := by
  have h : ∀ k : ℕ, 4*(11+k) < 3^(5+k) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show 5+k.succ=(5+k)+1 by omega, pow_succ]
      omega
  have hk : 11 + (p-11) = p := by omega
  have he : 5+(p-11)=p-6 := by omega
  have hh := h (p-11)
  rw [hk, he] at hh
  exact lt_of_lt_of_le hh (Nat.pow_le_pow_left hu (p-6))

/-- Under Hasse's bounds equality modulo p forces equal integral traces. -/
theorem trace_unique (a b p q : ℤ) (h : 16*q < p^2) (hp : 0<p)
    (ha : a^2 ≤ 4*q) (hb : b^2 ≤ 4*q) (hd : p ∣ a-b) : a=b := by
  obtain ⟨k,hk⟩ := hd
  have hdiff : (a-b)^2 < p^2 := by nlinarith [sq_nonneg (a+b)]
  have hk0 : k=0 := by
    rcases lt_trichotomy k 0 with hn | hz | hp'
    · have hbnd : p*k ≤ -p := by nlinarith [mul_nonneg (le_of_lt hp) (show 0≤ -k-1 by omega)]
      nlinarith [mul_nonneg (show 0≤ -(a-b)-p by omega) (show 0≤ -(a-b)+p by omega)]
    · exact hz
    · have hbnd : p≤p*k := by nlinarith [mul_nonneg (le_of_lt hp) (show 0≤k-1 by omega)]
      nlinarith [mul_nonneg (show 0≤a-b-p by omega) (show 0≤a-b+p by omega)]
  rw [hk0,mul_zero] at hk
  omega

end SepticSmooth
