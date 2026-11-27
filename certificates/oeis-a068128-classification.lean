import Mathlib

/-! Classificazione dei valori triangolari ottenibili come somma delle cifre
di infiniti numeri triangolari, per la congettura di Amarnath Murthy
nel commento 3 di OEIS A068128 (https://oeis.org/A068128). -/

namespace Deldor14.TriangularDigitSums

def triangle (n : ℕ) := (n+1).choose 2
def digitSum (n : ℕ) := (Nat.digits 10 n).sum
def targets (n : ℕ) : Set ℕ := {t | (∃ r, t=triangle r) ∧ digitSum t=triangle n}

private theorem succTriangle (n : ℕ) : triangle (n+1)=triangle n+(n+1) := by
  unfold triangle
  rw [Nat.choose_succ_succ (n+1) 1,Nat.choose_one_right]
  exact Nat.add_comm _ _
private theorem twice (n : ℕ) : 2*triangle n=n*(n+1) := by
  induction n with
  | zero => decide
  | succ n ih => rw [succTriangle]; nlinarith

private theorem blocks (u v k : ℕ) (h : u < 10^k) :
    digitSum (u+10^k*v)=digitSum u+digitSum v := by
  by_cases z : v=0
  · simp [z,digitSum]
  · have le := (Nat.digits_length_le_iff (by decide : 1<10) u).mpr h
    have e := Nat.digits_append_zeroes_append_digits (n:=u) (m:=v)
      (k:=k-(Nat.digits 10 u).length) (by decide : 1<10) (Nat.pos_of_ne_zero z)
    rw [show (Nat.digits 10 u).length+(k-(Nat.digits 10 u).length)=k by omega] at e
    simp [digitSum,← e]

private def represents (r n : ℕ) := digitSum (triangle r)=triangle n ∧ digitSum (2*r+1)=2*n+1

private theorem grow (r n limit : ℕ) (hr : represents r n) :
    ∃ s, represents s (n+2) ∧ limit < triangle s := by
  let k := limit+triangle r+(2*r+1)+1
  let p := 10^k
  have large : k < p := Nat.lt_pow_self (by decide : 1<10)
  have h₁ : triangle r < p := by dsimp [k] at large; omega
  have h₂ : 2*r+1 < p := by dsimp [k] at large; omega
  have h₃ : limit < p := by dsimp [k] at large; omega
  have e : triangle (r+2*p)=triangle r+p*((2*r+1)+p*2) := by
    have a := twice (r+2*p)
    have b := twice r
    nlinarith
  refine ⟨r+2*p,⟨?_,?_⟩,?_⟩
  · rw [e,blocks _ _ k h₁,blocks _ _ k h₂,hr.1,hr.2,succTriangle,succTriangle]
    have : digitSum 2=2 := by decide
    omega
  · rw [show 2*(r+2*p)+1=(2*r+1)+p*4 by ring,blocks _ _ k h₂,hr.2]
    have : digitSum 4=4 := by decide
    omega
  · rw [e]
    nlinarith

private theorem seed (n : ℕ) : ∃ r, represents r n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => exact ⟨0,by unfold represents; decide⟩
    | 1 => exact ⟨1,by unfold represents; decide⟩
    | k+2 =>
      obtain ⟨r,h⟩ := ih k (by omega)
      obtain ⟨s,hs,_⟩ := grow r k 0 h
      exact ⟨s,hs⟩

theorem infinite_from_two (n : ℕ) (hn : 2≤n) : (targets n).Infinite := by
  obtain ⟨k,rfl⟩ : ∃ k,n=k+2 := ⟨n-2,by omega⟩
  obtain ⟨r,hr⟩ := seed k
  apply Set.infinite_of_forall_exists_gt
  intro limit
  obtain ⟨s,hs,large⟩ := grow r k limit hr
  exact ⟨triangle s,⟨⟨s,rfl⟩,hs.1⟩,large⟩

private theorem vanishes (l : List ℕ) (h : l.sum=0) : Nat.ofDigits 10 l=0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.sum_cons,Nat.add_eq_zero_iff] at h
    simp [Nat.ofDigits_cons,h.1,ih h.2]
private theorem single (l : List ℕ) (h : l.sum=1) : ∃ k, Nat.ofDigits 10 l=10^k := by
  induction l with
  | nil => simp at h
  | cons d l ih =>
    simp only [List.sum_cons] at h
    by_cases z : d=0
    · obtain ⟨k,hk⟩ := ih (by omega)
      exact ⟨k+1,by simp [Nat.ofDigits_cons,z,hk,pow_succ,Nat.mul_comm]⟩
    · exact ⟨0,by rw [Nat.ofDigits_cons,vanishes l (by omega)]; simp; omega⟩

private theorem primeGap (k : ℕ) (hk : 2≤k) : 2*2^k+1 < 5^k := by
  induction k,hk using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [pow_succ,pow_succ]; omega

private theorem onlySmall (r k : ℕ) (h : triangle r=10^k) : k≤1 := by
  have eq := twice r
  rw [h,show (10:ℕ)=2*5 by decide,mul_pow] at eq
  have dvd : 5^k ∣ r*(r+1) := ⟨2*2^k,by rw [← eq]; ring⟩
  have hp : Nat.Prime 5 := by decide
  have split : 5^k ∣ r ∨ 5^k ∣ r+1 := by
    by_cases hd : 5 ∣ r
    · have c : Nat.Coprime 5 (r+1) := hp.coprime_iff_not_dvd.mpr (by omega)
      exact Or.inl ((c.pow_left k).dvd_of_dvd_mul_right dvd)
    · have c := hp.coprime_iff_not_dvd.mpr hd
      exact Or.inr ((c.pow_left k).dvd_of_dvd_mul_left dvd)
  have hr : 0<r := by
    by_contra! z
    have : r=0 := by omega
    simp [this] at eq
  have lower : 5^k ≤ r+1 := by
    rcases split with v|v
    · have := Nat.le_of_dvd hr v; omega
    · exact Nat.le_of_dvd (by omega) v
  by_contra! hk
  have gap := primeGap k (by omega)
  have pos : 0<5^k := by positivity
  have strict : (2*2^k)*5^k < r*(r+1) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (by omega : 2*2^k < r) pos)
      (Nat.mul_le_mul_left r lower)
  nlinarith

theorem zero_target : targets 0 = {0} := by
  ext t
  constructor
  · rintro ⟨_,ht⟩
    have h : (Nat.digits 10 t).sum=0 := ht
    simpa only [Nat.ofDigits_digits,Set.mem_singleton_iff] using vanishes _ h
  · rintro rfl
    exact ⟨⟨0,rfl⟩,by decide⟩

theorem one_target : targets 1 = {1,10} := by
  ext t
  constructor
  · rintro ⟨⟨r,rfl⟩,ht⟩
    obtain ⟨k,hk⟩ := single (Nat.digits 10 (triangle r)) ht
    rw [Nat.ofDigits_digits] at hk
    have le := onlySmall r k hk
    interval_cases k <;> simp [hk]
  · intro ht
    rcases ht with ht|ht
    · subst t; exact ⟨⟨1,rfl⟩,by decide⟩
    · have e : t=10 := ht
      subst t; exact ⟨⟨4,rfl⟩,by decide⟩

theorem classification (n : ℕ) : (targets n).Infinite ↔ 2≤n := by
  refine ⟨fun h => ?_,infinite_from_two n⟩
  by_contra! small
  interval_cases n
  · exact h (zero_target ▸ Set.finite_singleton 0)
  · exact h (one_target ▸ (Set.finite_singleton 10).insert 1)

#print axioms zero_target
#print axioms one_target
#print axioms classification
end Deldor14.TriangularDigitSums
