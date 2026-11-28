import Mathlib

/-! Critical fibers of the normalized fifth and seventh power sums.
All group-theoretic conclusions work at the prime-square modulus. -/
namespace BealCritical

theorem quintic_center {R : Type*} [CommRing R] (a b : R) :
    16*(a^5+b^5)-(a+b)^5 = 5*(a+b)*(a-b)^2*(3*a^2+2*a*b+3*b^2) := by ring

theorem quintic_fourth {R : Type*} [CommRing R] (a b : R) :
    4*(a^5+b^5)+(a+b)^5 = 5*(a+b)*(a^2+b^2)^2 := by ring

theorem septic_center {R : Type*} [CommRing R] (a b : R) :
    64*(a^7+b^7)-(a+b)^7 =
      7*(a+b)*(a-b)^2*(9*a^4+8*a^3*b+14*a^2*b^2+8*a*b^3+9*b^4) := by ring

theorem septic_sixth {R : Type*} [CommRing R] (a b : R) :
    27*(a^7+b^7)+(a+b)^7 = 7*(a+b)*(4*a^2+5*a*b+4*b^2)*(a^2-a*b+b^2)^2 := by ring

theorem septic_third {R : Type*} [CommRing R] (a b : R) :
    (a+b)^7-(a^7+b^7)=7*(a+b)*a*b*(a^2+a*b+b^2)^2 := by ring

theorem euler_sq {p : ℕ} (hp : p.Prime) {x : ZMod (p^2)} (hx : IsUnit x) :
    (x^p)^(p-1)=1 := by
  obtain ⟨u,rfl⟩ := hx
  have ht : (p^2).totient = p*(p-1) := by simpa using Nat.totient_prime_pow_succ hp 1
  rw [←pow_mul, ←ht]
  simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
    congrArg (fun z : (ZMod (p^2))ˣ => (z : ZMod (p^2))) (ZMod.pow_totient u)

theorem forced_wieferich {p j : ℕ} (hp : p.Prime) (hj : (2*j).Coprime p)
    {s u v : ZMod (p^2)} (hs : IsUnit s) (hu : IsUnit u) (hv : IsUnit v)
    (h : (s^j*v^p)^2 = (u^p)^2) : s^(p-1)=1 := by
  have h₁ := congrArg (fun a : ZMod (p^2) => a^(p-1)) h
  change ((s^j*v^p)^2)^(p-1) = ((u^p)^2)^(p-1) at h₁
  rw [pow_right_comm (s^j*v^p), pow_right_comm (u^p), mul_pow,
      euler_sq hp hu,euler_sq hp hv,mul_one,one_pow,pow_right_comm s] at h₁
  have ho₁ : orderOf (s^(p-1)) ∣ 2*j := by
    apply orderOf_dvd_iff_pow_eq_one.mpr
    rw [Nat.mul_comm,pow_mul]; exact h₁
  have ho₂ : orderOf (s^(p-1)) ∣ p := by
    apply orderOf_dvd_iff_pow_eq_one.mpr
    rw [pow_right_comm]; exact euler_sq hp hs
  apply orderOf_eq_one_iff.mp
  have hd := Nat.dvd_gcd ho₁ ho₂
  rw [hj.gcd_eq_one] at hd
  exact Nat.dvd_one.mp hd

theorem square_zero_of_dvd {p n : ℕ} (h : p ∣ n) : (n : ZMod (p^2))^2=0 := by
  exact_mod_cast (ZMod.natCast_eq_zero_iff (n^2) (p^2)).mpr (pow_dvd_pow_of_dvd h 2)

/-- In a unit chart, a signed critical value suffices, even before a
    representative of the p-th root is known to be a unit. -/
theorem signed_fiber {p j : ℕ} (hp : p.Prime) (hj : (2*j).Coprime p)
    {s v : ZMod (p^2)} (hs : IsUnit s)
    (eqn : s^j*v^p = 1 ∨ s^j*v^p = -1) : s^(p-1)=1 := by
  have hm : IsUnit (s^j*v^p) := by
    rcases eqn with e|e <;> rw [e] <;> simp
  have hv := (isUnit_pow_iff hp.ne_zero).mp ((Commute.all _ _).isUnit_mul_iff.mp hm).2
  apply forced_wieferich hp hj hs (u:=1) isUnit_one hv
  rcases eqn with e|e <;> rw [e] <;> norm_num

theorem four_critical_fibers {p : ℕ} (hp : p.Prime) (hlarge : 11≤p)
    (a b v : ZMod (p^2)) (h : a+b=1) :
    ((a^5+b^5=v^p ∧ (a-b)^2=0) → (2:ZMod (p^2))^(p-1)=1) ∧
    ((a^5+b^5=v^p ∧ (a^2+b^2)^2=0) → (2:ZMod (p^2))^(p-1)=1) ∧
    ((a^7+b^7=v^p ∧ (a-b)^2=0) → (2:ZMod (p^2))^(p-1)=1) ∧
    ((a^7+b^7=v^p ∧ (a^2-a*b+b^2)^2=0) → (3:ZMod (p^2))^(p-1)=1) := by
  have co (m : ℕ) (hm : 0 < m) (lt : m < p) : m.Coprime p := by
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm lt)).symm
  have u₂ : IsUnit (2:ZMod (p^2)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow (a:=2) hp (by decide : 0<2)).mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have u₃ : IsUnit (3:ZMod (p^2)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow (a:=3) hp (by decide : 0<2)).mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨hv,hr⟩
    apply signed_fiber (j:=4) hp (co 8 (by decide) (by omega)) u₂ (v:=v)
    left
    have e := quintic_center a b
    rw [hv,h,hr] at e
    linear_combination e
  · rintro ⟨hv,hr⟩
    apply signed_fiber (j:=2) hp (co 4 (by decide) (by omega)) u₂ (v:=v)
    right
    have e := quintic_fourth a b
    rw [hv,h,hr] at e
    linear_combination e
  · rintro ⟨hv,hr⟩
    have hcp : (2*6).Coprime p := by
      have q := co 6 (by decide) (by omega)
      exact (co 2 (by decide) (by omega)).mul_left q
    apply signed_fiber (j:=6) hp hcp u₂ (v:=v)
    left
    have e := septic_center a b
    rw [hv,h,hr] at e
    linear_combination e
  · rintro ⟨hv,hr⟩
    apply signed_fiber (j:=3) hp (co 6 (by decide) (by omega)) u₃ (v:=v)
    right
    have e := septic_sixth a b
    rw [hv,h,hr] at e
    linear_combination e

end BealCritical

#print axioms BealCritical.forced_wieferich
#print axioms BealCritical.four_critical_fibers
