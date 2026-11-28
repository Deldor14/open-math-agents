import Mathlib

namespace PrimeSquareCube

theorem recover_ratio (u v : ℤ) :
    (-(144*v))^3 * u^2 = -(v^3) * (1728*u)^2 := by ring

theorem discriminant (u v : ℤ) :
    -16*(4*(3*v)^3 + 27*(2*u)^2) = -1728*(u^2+v^3) := by ring

theorem equalities :
    654^2 + 127^3 = (19:ℕ)^5 ∧ 588^2 + 23^3 = (71:ℕ)^3 ∧
    4785^2 + 136^3 = (71:ℕ)^4 ∧ 15312283^2+9262^3 = (113:ℕ)^7 := by norm_num

theorem power_obstruction {N p a h : ℕ} (hp : p.Prime) (hd : p ∣ N)
    (hs : ¬p^2 ∣ N) (hh : 2 ≤ h) : a^h ≠ N := by
  rintro rfl
  have ha := hp.dvd_of_dvd_pow hd
  exact hs ((pow_dvd_pow_of_dvd ha 2).trans (pow_dvd_pow a hh))

theorem no_square_root_is_a_power (a h : ℕ) (hh : 2 ≤ h) :
    a^h ≠ 654 ∧ a^h ≠ 588 ∧ a^h ≠ 4785 ∧ a^h ≠ 15312283 := by
  refine ⟨power_obstruction (p:=2) (by decide) (by decide) (by decide) hh,
    power_obstruction (p:=3) (by decide) (by decide) (by decide) hh,
    power_obstruction (p:=5) (by decide) (by decide) (by decide) hh,
    power_obstruction (p:=7) (by decide) (by decide) (by decide) hh⟩

theorem extra_equalities :
    2355^2 + 118^3 = (193:ℕ)^3 ∧ 6216^2 + 157^3 = (349:ℕ)^3 ∧
    9324^2 + 11^3 = (443:ℕ)^3 ∧ 3085855^2 + 7656^3 = (1777:ℕ)^4 := by norm_num

theorem no_extra_root_is_a_power (a h : ℕ) (hh : 2 ≤ h) :
    a^h ≠ 2355 ∧ a^h ≠ 6216 ∧ a^h ≠ 9324 ∧ a^h ≠ 3085855 := by
  refine ⟨power_obstruction (p:=3) (by decide) (by decide) (by decide) hh,
    power_obstruction (p:=3) (by decide) (by decide) (by decide) hh,
    power_obstruction (p:=7) (by decide) (by decide) (by decide) hh,
    power_obstruction (p:=5) (by decide) (by decide) (by decide) hh⟩

theorem integral_model_discriminant (v u : ℚ) :
    -8*(6*v/4)^3-27*(1+4*((u-1)/4))^2 = -27*(u^2+v^3) := by ring

end PrimeSquareCube
