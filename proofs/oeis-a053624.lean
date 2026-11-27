import OMAStatements.S_oeis_a053624
import Mathlib

namespace Deldor14.OddRecords
open OMA.S_oeis_a053624 Nat

private theorem cardPow (p e : ℕ) (hp : p.Prime) : (p^e).divisors.card=e+1 := by
  simp [Nat.divisors_prime_pow hp]

private theorem replacePrime (n p : ℕ) (term : IsTerm n) (hn : n≠0)
    (hp : p.Prime) (big : 5<p) (pd : p∣n) (five : ¬ 5∣n) : False := by
  let e := n.factorization p
  let u := ordCompl[p] n
  have split : p^e*u=n := Nat.ordProj_mul_ordCompl_eq_self n p
  have ud : u∣n := Nat.ordCompl_dvd n p
  have un : 0<u := Nat.ordCompl_pos p hn
  have oddU : Odd u := Odd.of_dvd_nat term.1 ud
  have hp5 : (5:ℕ).Prime := by decide
  have c₁ : Nat.Coprime (5^e) u := (hp5.coprime_iff_not_dvd.mpr (fun h => five (dvd_trans h ud))).pow_left e
  have c₂ : Nat.Coprime (p^e) u := (Nat.coprime_ordCompl hp hn).pow_left e
  have ep : 0<e := hp.factorization_pos_of_dvd hn pd
  have lt : 5^e*u < n := split ▸ Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left big ep.ne') un
  have absurd := term.2 _ (((by decide : Odd (5:ℕ)).pow).mul oddU) lt
  rw [← split,c₁.card_divisors_mul,c₂.card_divisors_mul,cardPow 5 e hp5,cardPow p e hp] at absurd
  omega

private theorem pure (e : ℕ) (term : IsTerm (3^e)) : e≤2 := by
  by_contra! large
  obtain ⟨j,rfl⟩ : ∃ j,e=j+3 := ⟨e-3,by omega⟩
  have cop : (5:ℕ).Coprime (3^(j+1)) := (show (5:ℕ).Coprime 3 by decide).pow_right _
  have lt : 5*3^(j+1) < 3^(j+3) := by
    calc
      _ < 9*3^(j+1) := Nat.mul_lt_mul_of_pos_right (by decide) (by positivity)
      _ = 3^(j+3) := by rw [show j+3=j+1+2 by omega,pow_add 3 (j+1) 2]; ring
  have h := term.2 _ ((by decide : Odd (5:ℕ)).mul (show Odd (3^(j+1):ℕ) from (by decide : Odd (3:ℕ)).pow)) lt
  rw [cop.card_divisors_mul,cardPow 3 _ (by decide),cardPow 3 _ (by decide)] at h
  have hc : (5:ℕ).divisors.card=2 := by decide
  rw [hc] at h
  omega

theorem result : type_of% @OMA.S_oeis_a053624.main := by
  intro n term h1 h3 h9
  have hn : n≠0 := by obtain ⟨j,hj⟩ := term.1; omega
  have hp3 : (3:ℕ).Prime := by decide
  by_cases hf : 5∣n
  · obtain ⟨j,hj⟩ := term.1; omega
  let u := ordCompl[3] n
  by_cases hu : u=1
  · have he := Nat.ordProj_mul_ordCompl_eq_self n 3
    change 3^(n.factorization 3)*u=n at he
    rw [hu,mul_one] at he
    have bound := pure _ (he ▸ term)
    interval_cases (n.factorization 3) <;> norm_num at he <;> omega
  · let p := u.minFac
    have hp : p.Prime := Nat.minFac_prime hu
    have pd : p∣u := Nat.minFac_dvd u
    have pn := dvd_trans pd (Nat.ordCompl_dvd n 3)
    have neq3 : p≠3 := by
      intro he
      have dv : 3 ∣ u := by simpa only [he] using pd
      exact Nat.not_dvd_ordCompl (p:=3) hp3 hn dv
    have neq2 : p≠2 := by intro h; have z : 2∣n := h ▸ pn; obtain ⟨j,hj⟩ := term.1; omega
    have neq5 : p≠5 := fun e => hf (e ▸ pn)
    have big : 5<p := by
      by_contra! sm
      interval_cases p <;> first | contradiction | norm_num at hp
    exact False.elim (replacePrime n p term hn hp big pn hf)
end Deldor14.OddRecords
theorem OMA.solution : type_of% @OMA.S_oeis_a053624.main := Deldor14.OddRecords.result
