import Mathlib

/-!
# Auxiliary primes in the quintic branch with 5 dividing the sum of bases

The hypotheses s^r=5(a+b) and a^5+b^5=(a+b)5t^r describe the
5-divisible cofactor branch of a primitive equal-quintic solution.
-/

namespace BealForcedPrimes

def polynomial {K : Type*} [CommRing K] (w : K) := 5*w^4+10*w^2+1

private theorem cover {K : Type*} [Field K] (a b s t k : K) (r : ℕ)
    (hd : a+b ≠ 0) (hs : s ≠ 0) (h₁ : s^r=k*(a+b))
    (h₂ : a^5+b^5=(a+b)*k*t^r) :
    polynomial ((a-b)/(a+b))=16*k^5*(t/s^4)^r := by
  have q : a^4-a^3*b+a^2*b^2-a*b^3+b^4=k*t^r := by
    apply mul_left_cancel₀ hd
    calc
      (a+b)*(a^4-a^3*b+a^2*b^2-a*b^3+b^4) = a^5+b^5 := by ring
      _ = (a+b)*(k*t^r) := by rw [h₂]; ring
  unfold polynomial
  rw [div_pow t, ← pow_mul s, Nat.mul_comm 4 r, pow_mul, h₁]
  have h₅ : k ≠ 0 := by
    intro h
    rw [h, zero_mul] at h₁
    exact pow_ne_zero r hs h₁
  field_simp [hd,h₅]
  linear_combination 16*q

private theorem three_values (p e : ℕ) [Fact p.Prime] (hp : 2*e=p-1) (he : 0<e)
    (z : ZMod p) : z^e=0 ∨ z^e=1 ∨ z^e= -1 := by
  by_cases hz : z=0
  · simp [hz, he.ne']
  · right
    apply sq_eq_one_iff.mp
    rw [← pow_mul, Nat.mul_comm, hp]
    exact ZMod.pow_card_sub_one_eq_one hz

private theorem obstruction (p e r : ℕ) [Fact p.Prime] (hp : 2*e=p-1) (he : 0<e)
    (her : e ∣ r) (h5 : (5 : ZMod p) ≠ 0)
    (bad : ∀ w : ZMod p, polynomial w ≠ 0 ∧ polynomial w ≠ 16*5^5 ∧ polynomial w ≠ -(16*5^5))
    (a b s t : ℕ) (h₁ : s^r=5*(a+b)) (h₂ : a^5+b^5=(a+b)*5*t^r) :
    p^r ∣ a+b := by
  have hp' : p.Prime := Fact.out
  have hs0 : (s : ZMod p)=0 := by
    by_contra hs
    have h₁' : (s : ZMod p)^r=5*((a:ZMod p)+b) := by exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) h₁
    have h₂' : (a:ZMod p)^5+(b:ZMod p)^5=((a:ZMod p)+b)*5*(t:ZMod p)^r := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) h₂
    have hd : (a:ZMod p)+b≠0 := by
      intro hh
      rw [hh,mul_zero] at h₁'
      exact pow_ne_zero r hs h₁'
    have h := cover _ _ _ _ 5 _ hd hs h₁' h₂'
    obtain ⟨j,hj⟩ := her
    rw [hj, Nat.mul_comm, pow_mul] at h
    have ⟨n0,n1,nm⟩ := bad (((a:ZMod p)-b)/(a+b))
    rcases three_values p e hp he (((t:ZMod p)/s^4)^j) with h0 | h1 | hm
    · apply n0; simpa [h0] using h
    · apply n1; simpa [h1] using h
    · apply nm; simpa [hm] using h
  have hs' : p ∣ s := (ZMod.natCast_eq_zero_iff _ _).mp hs0
  have hcop : Nat.Coprime p 5 := hp'.coprime_iff_not_dvd.mpr (by
    intro h
    exact h5 ((ZMod.natCast_eq_zero_iff 5 p).mpr h))
  apply (hcop.pow_left r).dvd_of_dvd_mul_left
  rw [← h₁]
  exact pow_dvd_pow_of_dvd hs' r

set_option maxRecDepth 4000 in
private theorem residues23 : ∀ w : ZMod 23, polynomial w ≠ 0 ∧
    polynomial w ≠ 16*5^5 ∧ polynomial w ≠ -(16*5^5) := by decide

set_option maxRecDepth 4000 in
private theorem residues59 : ∀ w : ZMod 59, polynomial w ≠ 0 ∧
    polynomial w ≠ 16*5^5 ∧ polynomial w ≠ -(16*5^5) := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
private theorem residues227 : ∀ w : ZMod 227, polynomial w ≠ 0 ∧
    polynomial w ≠ 16*5^5 ∧ polynomial w ≠ -(16*5^5) := by decide

set_option maxRecDepth 8000 in
theorem forced_prime_powers (a b s t r : ℕ)
    (h₁ : s^r=5*(a+b)) (h₂ : a^5+b^5=(a+b)*5*t^r) :
    (11 ∣ r → 23^r ∣ a+b) ∧ (29 ∣ r → 59^r ∣ a+b) ∧
    (113 ∣ r → 227^r ∣ a+b) := by
  let _ : Fact (Nat.Prime 23) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 59) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 227) := ⟨by decide⟩
  exact ⟨fun h => obstruction 23 11 r (by decide) (by decide) h (by decide) residues23 _ _ _ _ h₁ h₂,
    fun h => obstruction 59 29 r (by decide) (by decide) h (by decide) residues59 _ _ _ _ h₁ h₂,
    fun h => obstruction 227 113 r (by decide) (by decide) h (by decide) residues227 _ _ _ _ h₁ h₂⟩

/-- Direct quintic splitting: after writing a+b=5h the second factor is
5g with g congruent to b^4 modulo 5h. -/
theorem primitive_split {a b c r : ℕ} (ha : 0<a) (hc : a.Coprime b)
    (hd : 5 ∣ a+b) (he : a^5+b^5=c^r) :
    ∃ s t : ℕ, s^r=5*(a+b) ∧ a^5+b^5=(a+b)*5*t^r := by
  obtain ⟨h,hh⟩ := hd
  have hd : 5 ∣ a+b := ⟨h,hh⟩
  obtain ⟨f,hf⟩ := (show Odd 5 by decide).nat_add_dvd_pow_add_pow a b
  have hhz : (a:ℤ)+b=5*h := by exact_mod_cast hh
  let G : ℤ := (b:ℤ)^4-10*h*b^3+50*(h:ℤ)^2*b^2-125*(h:ℤ)^3*b+125*(h:ℤ)^4
  have hG : (f:ℤ)=5*G := by
    have hm : (a:ℤ)^5+(b:ℤ)^5=((a:ℤ)+b)*f := by exact_mod_cast hf
    apply mul_left_cancel₀ (show (a:ℤ)+b≠0 by positivity)
    rw [← hm]
    have hA : (a:ℤ)=5*h-b := by linarith
    rw [hA]
    unfold G
    ring
  have hdv : (5:ℤ) ∣ f := ⟨G,hG⟩
  have hdvn : 5 ∣ f := by exact_mod_cast hdv
  obtain ⟨g,hg⟩ := hdvn
  have hgz : (g:ℤ)=G := by
    have hz : (f:ℤ)=5*g := by exact_mod_cast hg
    linarith
  have hcop : (5*(a+b)).Coprime g := by
    by_contra hn
    obtain ⟨l,hl,hlp,hlg⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hld : l ∣ a+b := (hl.dvd_mul.mp hlp).elim (fun h5 => h5.trans hd) id
    have hlb : ¬ l ∣ b := fun h => (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨l,hl,(Nat.dvd_add_iff_left h).mpr hld,h⟩) hc
    have hG' : (g:ℤ)=(b:ℤ)^4+(a+b)*
        (-2*(b:ℤ)^3+10*h*b^2-25*(h:ℤ)^2*b+25*(h:ℤ)^3) := by
      rw [hgz, hhz]
      unfold G
      ring
    have hlz : (l:ℤ) ∣ (a:ℤ)+b := by exact_mod_cast hld
    have hgdiv : (l:ℤ) ∣ (g:ℤ) := by exact_mod_cast hlg
    rw [hG'] at hgdiv
    have hpow := (dvd_add_left (dvd_mul_of_dvd_left hlz _)).mp hgdiv
    have hpow' : l ∣ b^4 := by exact_mod_cast hpow
    exact hlb (hl.dvd_of_dvd_pow hpow')
  have hprod : (5*(a+b))*g=c^r := by
    rw [← he,hf,hg]
    ring
  obtain ⟨s,hs⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop.gcd_eq_one) hprod
  obtain ⟨t,ht⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop.symm.gcd_eq_one)
    ((mul_comm g _).trans hprod)
  exact ⟨s,t,hs.symm,by rw [hf,hg,ht]; ring⟩

/-- Applies directly to the primitive Beal equation. -/
theorem primitive_forced_primes {a b c r : ℕ} (ha : 0<a) (hc : a.Coprime b)
    (hd : 5 ∣ a+b) (he : a^5+b^5=c^r) :
    (11 ∣ r → 23^r ∣ a+b) ∧ (29 ∣ r → 59^r ∣ a+b) ∧
    (113 ∣ r → 227^r ∣ a+b) := by
  obtain ⟨s,t,h₁,h₂⟩ := primitive_split ha hc hd he
  exact forced_prime_powers a b s t r h₁ h₂

private theorem unramified_split {a b c r : ℕ} (ha : 0<a) (hc : a.Coprime b)
    (hd : ¬5 ∣ a+b) (he : a^5+b^5=c^r) :
    ∃ s t : ℕ, s^r=a+b ∧ a^5+b^5=(a+b)*t^r := by
  obtain ⟨f,hf⟩ := (show Odd 5 by decide).nat_add_dvd_pow_add_pow a b
  have hcop : (a+b).Coprime f := by
    by_contra hn
    obtain ⟨l,hl,hld,hlf⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hnb : ¬ l ∣ b := fun h => (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨l,hl,(Nat.dvd_add_iff_left h).mpr hld,h⟩) hc
    have hid : (f:ℤ)=5*(b:ℤ)^4+(a+b)*
        ((a+b)^3-5*(a+b)^2*b+10*(a+b)*b^2-10*(b:ℤ)^3) := by
      have hz : (a:ℤ)^5+(b:ℤ)^5=((a:ℤ)+b)*f := by exact_mod_cast hf
      apply mul_left_cancel₀ (show (a:ℤ)+b≠0 by positivity)
      rw [← hz]
      ring
    have hz : (l:ℤ) ∣ (f:ℤ) := by exact_mod_cast hlf
    have hlz : (l:ℤ) ∣ (a:ℤ)+b := by exact_mod_cast hld
    rw [hid] at hz
    have h := (dvd_add_left (dvd_mul_of_dvd_left hlz _)).mp hz
    have h' : l ∣ 5*b^4 := by exact_mod_cast h
    rcases hl.dvd_mul.mp h' with h5 | hb
    · exact hd ((Nat.prime_dvd_prime_iff_eq hl (by decide : Nat.Prime 5)).mp h5 ▸ hld)
    · exact hnb (hl.dvd_of_dvd_pow hb)
  have hprod := hf.symm.trans he
  obtain ⟨s,hs⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop.gcd_eq_one) hprod
  obtain ⟨t,ht⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop.symm.gcd_eq_one)
    ((mul_comm f _).trans hprod)
  exact ⟨s,t,hs.symm,by rw [hf,ht]⟩

set_option maxRecDepth 5000 in
private theorem other59 : ∀ w : ZMod 59,
    polynomial w=0 ∨ polynomial w=16 ∨ polynomial w= -16 → w=1 ∨ w= -1 := by decide

/-- Uniform first-case obstruction with no condition on 5 dividing a+b. -/
theorem divides_product_59 {a b c r : ℕ} (ha : 0<a) (hc : a.Coprime b)
    (he : a^5+b^5=c^r) (hr : 29 ∣ r) (hrpos : 0<r) : 59 ∣ a*b*c := by
  let _ : Fact (Nat.Prime 59) := ⟨by decide⟩
  have pp : Nat.Prime 59 := by decide
  have hlin (h : 59 ∣ a+b) : 59 ∣ c := by
    obtain ⟨f,hf⟩ := (show Odd 5 by decide).nat_add_dvd_pow_add_pow a b
    apply pp.dvd_of_dvd_pow
    rw [← he,hf]
    exact dvd_mul_of_dvd_left h _
  by_cases hd : 59 ∣ a+b
  · exact dvd_mul_of_dvd_right (hlin hd) _
  by_cases h5 : 5 ∣ a+b
  · have h := (primitive_forced_primes ha hc h5 he).2.1 hr
    exact (hd ((dvd_pow (dvd_refl 59) hrpos.ne').trans h)).elim
  obtain ⟨s,t,hs,ht⟩ := unramified_split ha hc h5 he
  have hd' : (a:ZMod 59)+b≠0 := by
    intro h
    apply hd
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    exact h
  have hs' : (s:ZMod 59)^r=1*((a:ZMod 59)+b) := by
    rw [one_mul]; exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 59) hs
  have ht' : (a:ZMod 59)^5+(b:ZMod 59)^5=((a:ZMod 59)+b)*1*(t:ZMod 59)^r := by
    rw [mul_one]; exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 59) ht
  have hs0 : (s:ZMod 59)≠0 := by
    intro h
    apply hd'
    simpa [h,zero_pow hrpos.ne'] using hs'.symm
  obtain ⟨j,hj⟩ := hr
  have h := cover _ _ _ _ 1 r hd' hs0 hs' ht'
  rw [hj,Nat.mul_comm,pow_mul] at h
  let W := ((a:ZMod 59)-b)/(a+b)
  have hW : polynomial W=0 ∨ polynomial W=16 ∨ polynomial W= -16 := by
    rcases three_values 59 29 (by decide) (by decide) (((t:ZMod 59)/s^4)^j) with h0|h1|hm
    · left; simpa [W,h0] using h
    · right; left; simpa [W,h1] using h
    · right; right; simpa [W,hm] using h
  rcases other59 W hW with h1|hm
  · have hz := (div_eq_iff hd').mp h1
    have hb : (2:ZMod 59)*b=0 := by linear_combination -hz
    have hb' : 59 ∣ b := (ZMod.natCast_eq_zero_iff _ _).mp
      ((mul_eq_zero.mp hb).resolve_left (by decide))
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hb' _) _
  · have hz := (div_eq_iff hd').mp hm
    have ha' : (2:ZMod 59)*a=0 := by linear_combination hz
    have hda : 59 ∣ a := (ZMod.natCast_eq_zero_iff _ _).mp
      ((mul_eq_zero.mp ha').resolve_left (by decide))
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hda _) _

#print axioms primitive_forced_primes
#print axioms divides_product_59

end BealForcedPrimes
