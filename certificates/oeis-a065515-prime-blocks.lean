import Mathlib

/-!
# A065515: Number of prime powers ≤ n

Source: https://oeis.org/A065515
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of prime powers `≤ n`, counting `1 = p⁰` (offset `1`: `1, 2, 3, 4, 5, 5, …`).
Conjecture (Chayim Lowen, OEIS, 2015): `a(n) ≥ π(A069623(n)) + π(n) + 1`, where A069623(n) is the
number of perfect powers `≤ n` (counting `1`).

## Encoding

* Prime powers: `1` together with Mathlib's `IsPrimePow`. Perfect powers: `1` together with the
  numbers `m^k`, `m ≥ 2`, `k ≥ 2`.
* `π` is `Nat.primeCounting`. The statement is for all `n ≥ 1` (checked numerically for
  `n < 20000`).
-/

namespace OMA.S_oeis_a065515

/-- `a n`: number of prime powers (including `1`) in `[1, n]`. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter fun m => m = 1 ∨ IsPrimePow m).card

/-- `m` is a perfect power (including `1`). -/
def IsPerfectPower (m : ℕ) : Prop := m = 1 ∨ ∃ b k : ℕ, 2 ≤ b ∧ 2 ≤ k ∧ m = b ^ k

/-- A069623: number of perfect powers in `[1, n]`. -/
noncomputable def A069623 (n : ℕ) : ℕ :=
  Set.ncard {m : ℕ | 1 ≤ m ∧ m ≤ n ∧ IsPerfectPower m}

end OMA.S_oeis_a065515

namespace Deldor14.PrimePowerCount
open Finset OMA.S_oeis_a065515
private def block (m e : ℕ) := m.primesLE.image (fun p => p^e)
private theorem block_card (m e : ℕ) (he : e≠0) : (block m e).card=m.primeCounting := by
  rw [block,card_image_of_injective _ (Nat.pow_left_injective he),Nat.primesLE_card_eq_primeCounting]
private theorem separate (m e k f : ℕ) (he : e≠0) (hf : f≠0) (unequal : e≠f) :
    Disjoint (block m e) (block k f) := by
  apply disjoint_left.mpr
  intro v hv hv'
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hv
  obtain ⟨q,hq,eq⟩ := mem_image.mp hv'
  exact unequal (((Nat.prime_of_mem_primesLE hp).pow_inj' (Nat.prime_of_mem_primesLE hq) he hf eq.symm).2)
private theorem one_out (m e : ℕ) (he : e≠0) : 1 ∉ block m e := by
  rintro h
  obtain ⟨p,hp,eq⟩ := mem_image.mp h
  exact (one_lt_pow₀ (Nat.prime_of_mem_primesLE hp).one_lt he).ne' eq
private theorem member {m e n v : ℕ} (he : 0<e) (max : m^e≤n) (hv : v∈block m e) :
    v ∈ (Icc 1 n).filter (fun x => x=1 ∨ IsPrimePow x) := by
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hv
  obtain ⟨pm,prime⟩ := Nat.mem_primesLE.mp hp
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.one_le_pow _ _ prime.pos,
    (Nat.pow_le_pow_left pm e).trans max⟩,Or.inr ((isPrimePow_nat_iff _).mpr ⟨p,e,prime,he,rfl⟩)⟩

theorem primes_squares_cubes (n s c : ℕ) (hn : 1≤n) (hs : s^2≤n) (hc : c^3≤n) :
    Nat.primeCounting n+Nat.primeCounting s+Nat.primeCounting c+1≤a n := by
  let B := (block n 1 ∪ block s 2) ∪ block c 3
  have ab := separate n 1 s 2 (by decide) (by decide) (by decide)
  have ac := separate n 1 c 3 (by decide) (by decide) (by decide)
  have bc := separate s 2 c 3 (by decide) (by decide) (by decide)
  have one : 1 ∉ B := by
    simp only [B,mem_union,not_or]
    exact ⟨⟨one_out n 1 (by decide),one_out s 2 (by decide)⟩,one_out c 3 (by decide)⟩
  have size : (insert 1 B).card=Nat.primeCounting n+Nat.primeCounting s+Nat.primeCounting c+1 := by
    rw [card_insert_of_notMem one]
    dsimp [B]
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨ac,bc⟩),card_union_of_disjoint ab,
      block_card n 1 (by decide),block_card s 2 (by decide),block_card c 3 (by decide)]
  rw [←size,a]
  apply card_le_card
  intro v hv
  simp only [B,mem_insert,mem_union] at hv
  rcases hv with rfl | ((h|h)|h)
  · exact mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,hn⟩,Or.inl rfl⟩
  · exact member (by decide : 0<1) (by simp) h
  · exact member (by decide : 0<2) hs h
  · exact member (by decide : 0<3) hc h
#print axioms primes_squares_cubes
end Deldor14.PrimePowerCount
