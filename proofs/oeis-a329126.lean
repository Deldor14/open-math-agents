import OMAStatements.S_oeis_a329126
import Mathlib

/-! The formal definition does not bound each digit by the radix. Thus the
single decimal digit 2 is permitted even when read at base 2. This only
refutes the catalogue translation, not the binary-digit OEIS question. -/
namespace Deldor14.BaseDigitTranslation
open OMA.S_oeis_a329126
private lemma digit_two : Nat.digits 10 2 = [2] := by decide
private lemma digit_one : Nat.digits 10 1 = [1] := by decide
private lemma value : a 2 = 2 := by
  unfold a
  let S : Set ℕ := {m | 0 < m ∧ ∀ b ≥ 2, 2 ∣ Nat.ofDigits b (Nat.digits 10 m)}
  change sInf S = 2
  have member : 2 ∈ S := by
    refine ⟨by decide,?_⟩
    intro b _
    simp [digit_two,Nat.ofDigits]
  apply le_antisymm (Nat.sInf_le member)
  have minimal : sInf S ∈ S := Nat.sInf_mem ⟨2,member⟩
  obtain ⟨hp,hd⟩ := minimal
  by_contra! h
  have e : sInf S=1 := by omega
  have bad := hd 2 (by decide)
  rw [e,digit_one] at bad
  exact (by decide : ¬2 ∣ Nat.ofDigits 2 [1]) bad
theorem refute : ¬(type_of% @OMA.S_oeis_a329126.main) := by
  intro h
  have e := h 2 (by decide)
  rw [value,digit_two] at e
  exact (by decide : ¬ ([2] : List ℕ).count 1 = 2) e
end Deldor14.BaseDigitTranslation
theorem OMA.disproof : ¬(type_of% @OMA.S_oeis_a329126.main) := Deldor14.BaseDigitTranslation.refute
