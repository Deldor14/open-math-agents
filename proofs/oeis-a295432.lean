import OMAStatements.S_oeis_a295432
import Mathlib

namespace Deldor14.FactorialQuotient
open Finset

private abbrev v (p m : ℕ) := m.factorial.factorization p
private def left (n : ℕ) := 6*(6*n+1)*(12*n-1)*((6*n).factorial*(6*n).factorial*(4*n).factorial*n.factorial)
private def right (n : ℕ) := (12*n).factorial*(3*n).factorial*(2*n).factorial
private theorem lval (n p : ℕ) (hn : 0<n) : (left n).factorization p =
    Nat.factorization 6 p+(6*n+1).factorization p+(12*n-1).factorization p+v p (6*n)+v p (6*n)+v p (4*n)+v p n := by
  have pos : 12*n-1≠0 := by omega
  unfold left v
  simp (disch := positivity) only [Nat.factorization_mul,Finsupp.add_apply]
  omega
private theorem rval (n p : ℕ) : (right n).factorization p=v p (12*n)+v p (3*n)+v p (2*n) := by
  unfold right v
  rw [Nat.factorization_mul (by positivity) (by positivity),Nat.factorization_mul (by positivity) (by positivity)]
  simp
private theorem saving (p n : ℕ) (hp : p.Prime) (hn : 0<n) : (p-1)*v p n<n := by
  have digitsPos (m : ℕ) (hm : 0 < m) : 0<(Nat.digits p m).sum := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      rw [Nat.digits_def' hp.one_lt hm,List.sum_cons]
      by_cases q : m/p=0
      · have lt := (Nat.div_eq_zero_iff.mp q).resolve_left hp.ne_zero
        rw [Nat.mod_eq_of_lt lt]
        omega
      · have z := ih (m/p) (Nat.div_lt_self hm hp.one_lt) (Nat.pos_of_ne_zero q)
        omega
  have z := Nat.sub_one_mul_factorization_factorial (n:=n) hp
  have h := digitsPos n hn
  unfold v
  omega
private theorem small (n p : ℕ) (hn : 0<n) (hp : p=2 ∨ p=3) :
    (left n).factorization p≤(right n).factorization p := by
  rw [lval n p hn,rval]
  have sp (m : ℕ) (pr : m.Prime) (u : ℕ) : v m (m*u)=v m u+u := Nat.factorization_factorial_mul pr
  rcases hp with rfl|rfl
  · have f : Nat.factorization 6 2=1 := by
      rw [show 6=2*3 by decide,Nat.factorization_mul (by decide) (by decide),Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)];simp [Nat.prime_two.factorization]
    rw [f,Nat.factorization_eq_zero_of_not_dvd (by omega : ¬2 ∣ 6*n+1),
      Nat.factorization_eq_zero_of_not_dvd (by omega : ¬2 ∣ 12*n-1)]
    have u := saving 2 n Nat.prime_two hn
    rw [show 12*n=2*(6*n) by omega,sp 2 Nat.prime_two (6*n),show 6*n=2*(3*n) by omega,
      sp 2 Nat.prime_two (3*n),show 4*n=2*(2*n) by omega,sp 2 Nat.prime_two (2*n),sp 2 Nat.prime_two n]
    omega
  · have f : Nat.factorization 6 3=1 := by
      rw [show 6=2*3 by decide,Nat.factorization_mul (by decide) (by decide),Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2)];simp [Nat.prime_three.factorization]
    rw [f,Nat.factorization_eq_zero_of_not_dvd (by omega : ¬3 ∣ 6*n+1),
      Nat.factorization_eq_zero_of_not_dvd (by omega : ¬3 ∣ 12*n-1)]
    have u := saving 3 (2*n) Nat.prime_three (by omega)
    rw [show 12*n=3*(4*n) by omega,sp 3 Nat.prime_three (4*n),show 6*n=3*(2*n) by omega,
      sp 3 Nat.prime_three (2*n),sp 3 Nat.prime_three n]
    omega

private theorem residueTable (u : ℕ) :
    u/2+u/2+u/3+u/12+(if u%2=1 ∧ u%12≠3 then 1 else 0) ≤ u+u/4+u/6 := by
  have aux (k r : ℕ) (hr : r<12) :
      (r+12*k)/2+(r+12*k)/2+(r+12*k)/3+(r+12*k)/12+
        (if (r+12*k)%2=1 ∧ (r+12*k)%12≠3 then 1 else 0) ≤ (r+12*k)+(r+12*k)/4+(r+12*k)/6 := by
    interval_cases r <;> split_ifs <;> omega
  simpa only [Nat.mod_add_div] using aux (u/12) (u%12) (Nat.mod_lt _ (by decide))

private theorem perPower (n q : ℕ) (hn : 0<n) (hq : 5≤q) :
    (if q ∣ 6*n+1 then 1 else 0)+(if q ∣ 12*n-1 then 1 else 0)+
      (6*n)/q+(6*n)/q+(4*n)/q+n/q ≤ (12*n)/q+(3*n)/q+(2*n)/q := by
  let u := (12*n)/q
  have hpos : 0<q := by omega
  have div (a b : ℕ) (hb : 0<b) (hab : b*a=12) : u/b=(a*n)/q := by
    dsimp [u]
    rw [Nat.div_div_eq_div_mul,mul_comm q b,← hab,mul_assoc,Nat.mul_div_mul_left _ _ hb]
  have tab := residueTable u
  rw [div 6 2 (by decide) (by decide),div 4 3 (by decide) (by decide),
    div 1 12 (by decide) (by decide),div 3 4 (by decide) (by decide),div 2 6 (by decide) (by decide),one_mul] at tab
  change _ ≤ u+_+_
  by_cases h₁ : q ∣ 6*n+1
  · have h₂ : ¬ q ∣ 12*n-1 := by
      intro d
      have v := Nat.dvd_sub (dvd_mul_of_dvd_right h₁ 2) d
      rw [show 2*(6*n+1)-(12*n-1)=3 by omega] at v
      have := Nat.le_of_dvd (by decide : 0<3) v
      omega
    obtain ⟨w,e⟩ := h₁
    have wp : 0 < w := by
      by_contra h
      have zero : w=0 := by omega
      rw [zero,mul_zero] at e
      omega
    obtain ⟨t,rfl⟩ : ∃ t,w=t+1 := ⟨w-1,by omega⟩
    have e' := e
    rw [Nat.mul_add_one] at e'
    have eu : u=2*t+1 := by
      dsimp [u]
      apply le_antisymm
      · apply Nat.le_of_lt_succ
        apply (Nat.div_lt_iff_lt_mul hpos).mpr
        nlinarith
      · apply (Nat.le_div_iff_mul_le hpos).mpr
        nlinarith
    have evenT : t%2=0 := by
      by_contra h
      have d : 2 ∣ t+1 := by omega
      have dd : 2 ∣ 6*n+1 := e ▸ dvd_mul_of_dvd_right d _
      omega
    rw [if_pos (show q ∣ 6*n+1 from ⟨t+1,e⟩),if_neg h₂]
    rw [if_pos (by constructor <;> omega)] at tab
    omega
  · rw [if_neg h₁]
    by_cases h₂ : q ∣ 12*n-1
    · obtain ⟨w,e⟩ := h₂
      have eu : u=w := by
        dsimp [u]
        apply le_antisymm
        · apply Nat.le_of_lt_succ
          apply (Nat.div_lt_iff_lt_mul hpos).mpr
          nlinarith [show 12*n=12*n-1+1 by omega]
        · apply (Nat.le_div_iff_mul_le hpos).mpr
          nlinarith [show 12*n=12*n-1+1 by omega]
      have nod (s : ℕ) (hs : s=2 ∨ s=3) : ¬s ∣ w := by
        intro dv
        have dd : s ∣ 12*n-1 := e ▸ dvd_mul_of_dvd_right dv _
        rcases hs with rfl|rfl <;> omega
      have h2 := nod 2 (Or.inl rfl)
      have h3 := nod 3 (Or.inr rfl)
      rw [if_pos (show q ∣ 12*n-1 from ⟨w,e⟩)]
      rw [if_pos (by constructor <;> omega)] at tab
      omega
    · rw [if_neg h₂]
      split_ifs at tab <;> omega

private theorem large (n p : ℕ) (hn : 0<n) (pr : p.Prime) (hp : 5≤p) :
    (left n).factorization p≤(right n).factorization p := by
  let b := 12*n+4
  have lb (m : ℕ) (hm : m<b) : Nat.log p m<b := (Nat.log_le_self p m).trans_lt hm
  have leg (m : ℕ) (hm : m<b) := Nat.factorization_factorial pr (lb m hm)
  have posval (m : ℕ) (h : 0 < m) (hm : m<b) :
      m.factorization p=∑ i ∈ Ico 1 b,if p^i ∣ m then 1 else 0 := by
    rw [sum_boole,Nat.factorization_eq_card_pow_dvd_of_lt pr h (Nat.lt_pow_of_log_lt pr.one_lt (lb m hm))]
    simp
  have nd : ¬p ∣ 6 := by
    rw [show 6=2*3 by decide]
    intro e
    rcases pr.dvd_mul.mp e with v|v
    · have := Nat.le_of_dvd (by decide : 0<2) v;omega
    · have := Nat.le_of_dvd (by decide : 0<3) v;omega
  rw [lval n p hn,rval,Nat.factorization_eq_zero_of_not_dvd nd,zero_add,
    posval (6*n+1) (by omega) (by dsimp [b];omega),posval (12*n-1) (by omega) (by dsimp [b];omega)]
  unfold v
  simp only [leg (6*n) (by dsimp [b];omega),leg (4*n) (by dsimp [b];omega),leg n (by dsimp [b];omega),
    leg (12*n) (by dsimp [b];omega),leg (3*n) (by dsimp [b];omega),leg (2*n) (by dsimp [b];omega),← sum_add_distrib]
  apply sum_le_sum
  intro i hi
  exact perPower n (p^i) hn (hp.trans (Nat.le_self_pow (by have := (mem_Ico.mp hi).1;omega) p))

theorem result : type_of% @OMA.S_oeis_a295432.main := by
  intro n hn
  have z : 12*n-1≠0 := by omega
  apply (Nat.factorization_prime_le_iff_dvd (by change left n≠0;unfold left;positivity)
    (by change right n≠0;unfold right;positivity)).mp
  intro p pr
  by_cases h : p=2 ∨ p=3
  · exact small n p hn h
  · have q := pr.two_le
    have p4 : p≠4 := by rintro rfl;exact (by decide : ¬Nat.Prime 4) pr
    exact large n p hn pr (by omega)
end Deldor14.FactorialQuotient
theorem OMA.solution : type_of% @OMA.S_oeis_a295432.main := Deldor14.FactorialQuotient.result
