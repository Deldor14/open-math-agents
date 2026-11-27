import OMAStatements.S_oeis_a285802
import Mathlib

namespace Deldor14.Seven
open OMA.S_oeis_a285802

/-- The units and tens digits suffice after cancelling trailing zeroes.
Only the final two digits of the input matter. -/
private theorem residues : ∀ r : Fin 100, r.val%10≠0 → ∃ k : Fin 36,
    0<k.val ∧ ((k.val*r.val)%10=7 ∨ (k.val*r.val)%100/10=7) := by
  decide +kernel

private theorem last (x : ℕ) (e : x%10=7) : HasSeven x := by
  have h : x≠0 := by omega
  unfold HasSeven
  rw [Nat.digits_eq_cons_digits_div (by decide) h]
  simp [e]
private theorem tens (x : ℕ) (e : x%100/10=7) : HasSeven x := by
  have h : x≠0 := by rintro rfl;contradiction
  have d : x/10%10=7 := by simpa only [show 100=10*10 by decide,Nat.mod_mul_right_div_self] using e
  unfold HasSeven
  rw [Nat.digits_eq_cons_digits_div (by decide) h]
  exact List.mem_cons_of_mem _ (last _ d)

private theorem upper (n : ℕ) (hn : 1≤n) : ∃ k : ℕ, 1≤k ∧ k≤35 ∧ HasSeven (k*n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases div : n%10=0
    · obtain ⟨k,hk,le,hit⟩ := ih (n/10) (by omega) (by omega)
      refine ⟨k,hk,le,?_⟩
      have eq : k*n=10*(k*(n/10)) := by calc
        _ = k*(10*(n/10)) := congrArg (k*·) (by omega)
        _ = _ := by ring
      unfold HasSeven at *
      rw [eq,Nat.digits_base_mul (by decide : 1<10) (Nat.mul_pos hk (by omega))]
      exact List.mem_cons_of_mem _ hit
    · let r : Fin 100 := ⟨n%100,Nat.mod_lt _ (by decide)⟩
      have rd : r.val%10≠0 := by simpa [r,Nat.mod_mod_of_dvd n (by decide : 10 ∣ 100)] using div
      obtain ⟨k,hk,e⟩ := residues r rd
      refine ⟨k.val,hk,by have := k.isLt;omega,?_⟩
      have eq100 : (k.val*r.val)%100=(k.val*n)%100 := ((Nat.mod_modEq n 100).mul_left k.val)
      rcases e with e|e
      · exact last _ (by rw [← Nat.mod_mod_of_dvd (k.val*n) (by decide : 10 ∣ 100),← eq100,Nat.mod_mod_of_dvd _ (by decide : 10 ∣ 100)];exact e)
      · exact tens _ (eq100 ▸ e)

theorem OMAresult : type_of% @OMA.S_oeis_a285802.main := by
  refine ⟨upper,?_,?_⟩
  · intro k lo hi
    unfold HasSeven
    interval_cases k <;> decide
  · unfold HasSeven;decide
end Deldor14.Seven
theorem OMA.solution : type_of% @OMA.S_oeis_a285802.main := Deldor14.Seven.OMAresult
