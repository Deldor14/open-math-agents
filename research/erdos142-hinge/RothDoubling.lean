import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic

open Finset

namespace Erdos142Scale

/-- An AP-free set in an odd interval misses its first, middle, or last point. -/
theorem odd_interval (m : ℕ) (hm : 0 < m) :
    rothNumberNat (2*m+1) ≤ 2*rothNumberNat m := by
  obtain ⟨A, hA, hcard, hfree⟩ := rothNumberNat_spec (2*m+1)
  have bound (a b : ℕ) (h : A ⊆ Ico a (a+m) ∪ Ico b (b+m)) :
      rothNumberNat (2*m+1) ≤ 2*rothNumberNat m := by
    rw [← hcard]
    calc
      A.card ≤ addRothNumber (Ico a (a+m) ∪ Ico b (b+m)) := hfree.le_addRothNumber h
      _ ≤ addRothNumber (Ico a (a+m)) + addRothNumber (Ico b (b+m)) :=
        addRothNumber_union_le _ _
      _ = 2*rothNumberNat m := by simp [addRothNumber_Ico, two_mul]
  have pos (x : ℕ) (hx : x ∈ A) : x < 2*m+1 := mem_range.mp (hA hx)
  by_cases h0 : 0 ∈ A
  · by_cases hmA : m ∈ A
    · have h2 : 2*m ∉ A := by
        intro h
        have eqn := threeAPFree_iff_eq_right.mp hfree h0 hmA h (by omega)
        omega
      apply bound 0 m
      intro x hx
      have := pos x hx
      have hne : x ≠ 2*m := fun he => h2 (he ▸ hx)
      simp only [mem_union, mem_Ico]
      omega
    · apply bound 0 (m+1)
      intro x hx
      have := pos x hx
      have hne : x ≠ m := fun he => hmA (he ▸ hx)
      simp only [mem_union, mem_Ico]
      omega
  · apply bound 1 (m+1)
    intro x hx
    have := pos x hx
    have hne : x ≠ 0 := fun he => h0 (he ▸ hx)
    simp only [mem_union, mem_Ico]
    omega

theorem padded_power (m j : ℕ) (hm : 0 < m) :
    rothNumberNat (2^j*(m+1)-1) ≤ 2^j * rothNumberNat m := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hp : 0 < 2^j := pow_pos (by decide) _
    have hs : 1 < 2^j*(m+1) := by nlinarith
    have h := odd_interval (2^j*(m+1)-1) (by omega)
    rw [pow_succ]
    have he : 2^j * 2 * (m+1) - 1 = 2*(2^j*(m+1)-1)+1 := by
      have hmul : 2^j * 2 * (m+1) = 2*(2^j*(m+1)) := by ring
      omega
    rw [he]
    calc
      _ ≤ 2 * rothNumberNat (2^j*(m+1)-1) := h
      _ ≤ 2 * (2^j * rothNumberNat m) := Nat.mul_le_mul_left 2 ih
      _ = _ := by ring

#print axioms odd_interval
#print axioms padded_power
end Erdos142Scale
