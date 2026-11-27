import Mathlib

/-!
# A319012: a(n) = Sum_{i=1..n} prime(n*(i - 1) + i).

Source: https://oeis.org/A319012
Credit: @sntntHb

Conjecture (stated on the OEIS page): `a(2)` and `a(3)` are the only terms that are perfect
squares (`a(2) = 9`, `a(3) = 36`).

Conventions:
- `prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`.
- The offset is 1, so the terms are `a(n)` for `n ≥ 1`.
-/

namespace OMA.S_oeis_a319012

/-- `a(n) = ∑_{i=1}^{n} prime(n*(i-1) + i)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, Nat.nth Nat.Prime (n * (i - 1) + i - 1)

end OMA.S_oeis_a319012

namespace Deldor14.PrimeSquares
open Finset OMA.S_oeis_a319012
/-- For all positive indices the parity of the term is opposite that of its index. -/
theorem parity_all (n : ℕ) (hn : 1 ≤ n) : a n ≡ n+1 [MOD 2] := by
  have mem : 1 ∈ Icc 1 n := mem_Icc.mpr ⟨le_rfl,hn⟩
  have term (i : ℕ) (hi : i ∈ Icc 1 n) :
      Nat.nth Nat.Prime (n*(i-1)+i-1) ≡ (if i=1 then 1 else 0)+1 [MOD 2] := by
    by_cases one : i=1
    · subst i
      simp [Nat.nth_prime_zero_eq_two] <;> rfl
    · let j := n*(i-1)+i-1
      have lo := (mem_Icc.mp hi).1
      have jp : 0 < j := by dsimp [j];omega
      have larger := (Nat.nth_strictMono Nat.infinite_setOfPred_prime) jp
      rw [Nat.nth_prime_zero_eq_two] at larger
      have prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j
      have odd := prime.odd_of_ne_two larger.ne'
      change Nat.nth Nat.Prime j ≡ _ [MOD 2]
      rw [if_neg one]
      exact Nat.odd_iff.mp odd
  have total := Nat.ModEq.sum term
  have right : (∑ i ∈ Icc 1 n, ((if i=1 then 1 else 0)+1))=n+1 := by
    rw [sum_add_distrib]
    simp [mem,Nat.card_Icc]
    <;> omega
  exact right ▸ total
/-- A square term at an even index is one modulo eight. At an odd index
it is divisible by four. -/
theorem square_restriction (n : ℕ) (hn : 1 ≤ n) (sq : IsSquare (a n)) :
    (Even n → a n % 8 = 1) ∧ (Odd n → a n % 4 = 0) := by
  obtain ⟨r,hr⟩ := sq
  have h := parity_all n hn
  change a n % 2=(n+1)%2 at h
  rw [hr] at h ⊢
  have table : ∀ i : Fin 8,
      ((i.val*i.val)%2=1 → (i.val*i.val)%8=1) ∧
      ((i.val*i.val)%2=0 → (i.val*i.val)%4=0) := by decide +kernel
  let i : Fin 8 := ⟨r%8,Nat.mod_lt _ (by decide)⟩
  have mod8 : (i.val*i.val)%8=(r*r)%8 := by dsimp [i];exact (Nat.mul_mod r r 8).symm
  have test := table i
  have dvd2 : 2 ∣ 8 := by decide
  have dvd4 : 4 ∣ 8 := by decide
  have h2 := congrArg (·%2) mod8
  have h4 := congrArg (·%4) mod8
  simp only [Nat.mod_mod_of_dvd _ dvd2] at h2
  simp only [Nat.mod_mod_of_dvd _ dvd4] at h4
  constructor
  · rintro ⟨k,hk⟩
    rw [← mod8]
    apply test.1
    omega
  · rintro ⟨k,hk⟩
    rw [← h4]
    apply test.2
    omega
#print axioms parity_all
#print axioms square_restriction
end Deldor14.PrimeSquares
