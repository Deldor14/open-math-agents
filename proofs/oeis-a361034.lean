import OMAStatements.S_oeis_a361034
import Mathlib

namespace Deldor14.FactorialParity
open OMA.S_oeis_a361034 Finset

private def bits (m : ℕ) := (Nat.digits 2 m).sum
private theorem bitsOne (m : ℕ) (hm : 0 < m) :
    0 < bits m ∧ (bits m=1 → ∃ k : ℕ, m=2^k) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases e : m=1
    · subst m; exact ⟨by decide,fun _ => ⟨0,rfl⟩⟩
    obtain ⟨pos,pow⟩ := ih (m/2) (by omega) (by omega)
    have recurrence : bits m=m%2+bits (m/2) := by
      unfold bits
      rw [Nat.digits_def' (by decide : 1<2) hm,List.sum_cons]
    constructor
    · omega
    · intro u
      obtain ⟨k,hk⟩ := pow (by omega)
      exact ⟨k+1,by rw [pow_succ,← hk]; omega⟩
private theorem bitsPow (k : ℕ) : bits (2^k)=1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    simpa [bits,pow_succ',Nat.digits_base_mul (by decide : 1<2) (by positivity : 0<2^k)] using ih
private def top (n : ℕ) := 2520*(4*n).factorial
private def bot (n : ℕ) := n.factorial*(n+2).factorial^3
private theorem vf (m : ℕ) : m.factorial.factorization 2+bits m=m := by
  have h := Nat.sub_one_mul_factorization_factorial (n:=m) Nat.prime_two
  have s := Nat.digit_sum_le 2 m
  simp only [bits]
  norm_num at h
  omega
private theorem bottom (n p : ℕ) : (bot n).factorization p =
    n.factorial.factorization p+3*(n+2).factorial.factorization p := by
  unfold bot
  rw [Nat.factorization_mul n.factorial_ne_zero (pow_ne_zero _ (n+2).factorial_ne_zero),Nat.factorization_pow,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
private theorem topVal (n p : ℕ) : (top n).factorization p =
    Nat.factorization 2520 p+(4*n).factorial.factorization p := by
  unfold top
  rw [Nat.factorization_mul (by decide) (4*n).factorial_ne_zero,Finsupp.add_apply]
private theorem twoVal (n : ℕ) :
    (top n).factorization 2+3=(bot n).factorization 2+3*bits (n+2) := by
  have d (m : ℕ) := Nat.factorization_factorial_mul (n:=m) Nat.prime_two
  rw [topVal,bottom,show Nat.factorization 2520 2=3 by
      rw [show 2520=(315:ℕ)*2^3 by decide,Nat.factorization_mul (by decide) (by decide),Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315),Nat.Prime.factorization_pow Nat.prime_two];simp,
    show 4*n=2*(2*n) by omega,d,d]
  have h := vf (n+2)
  omega

private theorem floors (n q : ℕ) (hq : 3≤q) :
    n/q+3*((n+2)/q) ≤ (4*n)/q+7/q := by
  by_cases sm : q≤7
  · have small (a u r : ℕ) (h1 : 3≤a) (h2 : a≤7) (hr : r<a) :
        (r+a*u)/a+3*((r+a*u+2)/a)≤(4*(r+a*u))/a+7/a := by
        interval_cases a <;> interval_cases r <;> omega
    simpa only [Nat.mod_add_div] using small q (n/q) (n%q) hq sm (Nat.mod_lt _ (by omega))
  have qp : 0<q := by omega
  let u := n/q
  have lo : u*q≤n := Nat.div_mul_le_self n q
  have hi : n<(u+1)*q := (Nat.div_lt_iff_lt_mul qp).mp (Nat.lt_succ_self _)
  rw [Nat.div_eq_of_lt (by omega : 7<q),Nat.add_zero]
  change u+3*((n+2)/q) ≤ _
  by_cases c : n+2<(u+1)*q
  · have cap : (n+2)/q<u+1 := (Nat.div_lt_iff_lt_mul qp).mpr c
    have h : 4*u≤(4*n)/q := (Nat.le_div_iff_mul_le qp).mpr (by nlinarith [lo])
    omega
  · have cap : (n+2)/q<u+2 := (Nat.div_lt_iff_lt_mul qp).mpr (by nlinarith [hi])
    have h : 4*u+3≤(4*n)/q := (Nat.le_div_iff_mul_le qp).mpr (by nlinarith)
    omega

private theorem oddLe (n p : ℕ) (hp : p.Prime) (hne : p≠2) :
    (bot n).factorization p ≤ (top n).factorization p := by
  let b := 4*n+10
  have leg (m : ℕ) (h : m<b) := Nat.factorization_factorial hp ((Nat.log_le_self p m).trans_lt h)
  have v7 : Nat.factorization 2520 p=((7:ℕ).factorial).factorization p := by
    have z : Nat.factorization 2 p=0 := by simp [Nat.prime_two.factorization,Ne.symm hne,hne]
    rw [show ((7:ℕ).factorial)=2*2520 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [z]
  rw [bottom,topVal,v7,leg n (by dsimp [b];omega),leg (n+2) (by dsimp [b];omega),
    leg (4*n) (by dsimp [b];omega),leg 7 (by dsimp [b];omega),Finset.mul_sum,← sum_add_distrib,← sum_add_distrib]
  apply sum_le_sum
  intro i hi
  have hp3 : 3≤p := by have := hp.two_le; omega
  have hi1 := (mem_Ico.mp hi).1
  have h := floors n (p^i) (hp3.trans (Nat.le_self_pow (by omega) p))
  omega
private theorem divides (n : ℕ) : bot n ∣ top n := by
  apply (Nat.factorization_prime_le_iff_dvd (by unfold bot; positivity) (by unfold top; positivity)).mp
  intro p hp
  by_cases he : p=2
  · subst p
    have t := twoVal n
    have h := (bitsOne (n+2) (by omega)).1
    omega
  · exact oddLe n p hp he
private theorem vquot (n : ℕ) : (a n).factorization 2+3=3*bits (n+2) := by
  have eq : a n*bot n=top n := Nat.div_mul_cancel (divides n)
  have tp : top n≠0 := by unfold top; positivity
  have bp : bot n≠0 := by unfold bot; positivity
  have ap : a n≠0 := fun h => tp (by rw [← eq,h,zero_mul])
  have t := twoVal n
  rw [← eq,Nat.factorization_mul ap bp,Finsupp.add_apply] at t
  omega
theorem result : type_of% @OMA.S_oeis_a361034.main := by
  intro n
  have eq : a n*bot n=top n := Nat.div_mul_cancel (divides n)
  have ap : a n≠0 := by
    intro z
    rw [z,zero_mul] at eq
    have hp : 0<top n := by unfold top; positivity
    omega
  have v := vquot n
  have z := Nat.factorization_eq_zero_iff (a n) 2
  simp only [Nat.prime_two,not_true_eq_false,false_or,ap,or_false] at z
  constructor
  · rintro ⟨u,hu⟩
    obtain ⟨k,hk⟩ := (bitsOne (n+2) (by omega)).2 (by have h := z.mpr (by omega);omega)
    exact ⟨k,by cases k <;> simp_all,by omega⟩
  · rintro ⟨k,hk,e⟩
    have p : 2≤2^k := Nat.le_self_pow (by omega) 2
    have b : bits (n+2)=1 := by rw [show n+2=2^k by omega,bitsPow]
    have nd := z.mp (by omega)
    exact ⟨a n/2,by omega⟩
end Deldor14.FactorialParity
theorem OMA.solution : type_of% @OMA.S_oeis_a361034.main := Deldor14.FactorialParity.result
