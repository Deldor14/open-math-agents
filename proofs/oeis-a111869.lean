import OMAStatements.S_oeis_a111869
import Mathlib

/-! Below the threshold a prime can occur only once in a binomial
coefficient. At the threshold Pascal's rule adds two entries of row p²,
both of which are divisible by p². -/
open Nat OMA.S_oeis_a111869

theorem OMA.solution : type_of% @OMA.S_oeis_a111869.main := by
  intro p hp htwo
  let j := (p^2-1)/2
  have odd := (hp.odd_of_ne_two htwo).pow (n:=2)
  have eq : 2*j+1=p^2 := by obtain ⟨t,ht⟩:=odd;dsimp [j];omega
  have hj : 0 < j := by have := hp.two_le; nlinarith [sq_nonneg (p:ℤ)]
  have dv : p ∣ p^2 := dvd_pow_self _ (by decide : 2≠0)
  have unit : ¬ p ∣ 1 := hp.not_dvd_one
  have no₀ : ¬ p ∣ j := by
    intro h
    apply unit
    have e := Nat.dvd_sub dv (dvd_mul_of_dvd_right h 2)
    rwa [show p^2-2*j=1 by omega] at e
  have no₁ : ¬ p ∣ j+1 := by
    intro h
    apply unit
    have e := Nat.dvd_sub (dvd_mul_of_dvd_right h 2) dv
    rwa [show 2*(j+1)-p^2=1 by omega] at e
  have chooseDiv (i : ℕ) (hi : 0 < i) (bound : i ≤ p^2) (nd : ¬ p ∣ i) : p^2 ∣ (p^2).choose i := by
    rw [hp.pow_dvd_iff_le_factorization (choose_ne_zero bound),factorization_choose_prime_pow hp bound hi.ne',factorization_eq_zero_of_not_dvd nd]
  have mem : j+1 ∈ {k : ℕ | 1 ≤ k ∧ p^2 ∣ (2*k).choose k} := by
    refine ⟨by omega,?_⟩
    rw [show 2*(j+1)=p^2+1 by omega,choose_succ_succ]
    exact dvd_add (chooseDiv j hj (by omega) no₀) (chooseDiv (j+1) (by omega) (by omega) no₁)
  have spec := Nat.sInf_mem (Set.nonempty_of_mem mem)
  change 1 ≤ a p ∧ p^2 ∣ (2*a p).choose (a p) at spec
  refine le_antisymm (Nat.sInf_le mem) ?_
  change j+1 ≤ a p
  by_contra! bad
  have le : ((2*a p).choose (a p)).factorization p ≤ 1 := factorization_choose_le_one (by omega)
  have ge := (hp.pow_dvd_iff_le_factorization (choose_ne_zero (by omega : a p ≤ 2*a p))).mp spec.2
  omega
