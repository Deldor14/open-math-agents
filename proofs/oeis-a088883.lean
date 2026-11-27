import OMAStatements.S_oeis_a088883
import Mathlib

open OMA.S_oeis_a088883

theorem OMA.solution : type_of% @OMA.S_oeis_a088883.main := by
  intro p hp hy
  by_cases hsmall : p≤3
  · interval_cases p <;> first | contradiction | norm_num [rev,Nat.digits_def'] at *
  have odd := hp.odd_of_ne_two (by omega)
  have h₃ : ¬ 3 ∣ p := fun h => (hp.eq_one_or_self_of_dvd 3 h).elim (by decide) (by omega)
  have hr : rev p ≡ p [MOD 3] := by
    have h := Nat.ofDigits_modEq' 10 1 3 (by decide) (Nat.digits 10 p).reverse
    rw [Nat.ofDigits_one,List.sum_reverse] at h
    exact h.trans (Nat.modEq_three_digits_sum p).symm
  have he := (show 10 ≡ 1 [MOD 3] by decide).pow (Nat.digits 10 p).length
  simp only [one_pow] at he
  by_contra! bad
  have hm : p % 3 = 2 := by obtain ⟨j,hj⟩ := odd; omega
  have hd : 3 ∣ p*10^(Nat.digits 10 p).length+rev p+2 := by
    apply Nat.dvd_of_mod_eq_zero
    have hex := (((Nat.ModEq.refl p).mul he).add hr).add (Nat.ModEq.refl 2)
    change _ % 3 = _ % 3 at hex
    simp only [mul_one] at hex
    omega
  have mag : 1 ≤ 10^(Nat.digits 10 p).length := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  have groot : 3 < p*10^(Nat.digits 10 p).length+rev p+2 := by nlinarith
  exact (hy.eq_one_or_self_of_dvd 3 hd).elim (by decide) (by omega)
