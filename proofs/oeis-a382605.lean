import OMAStatements.S_oeis_a382605
import Mathlib

namespace Deldor14.EqualSides
open OMA.S_oeis_a382605
private theorem triangle (n : ℕ) : 2*total n=n*(n+1) := by
  induction n with
  | zero => rfl
  | succ n h => rw [total];nlinarith
private theorem par (n : ℕ) : Even (total n) ↔ n%4=0 ∨ n%4=3 := by
  have eq := congrArg (fun x : ℕ => x%4) (triangle n)
  change (2*total n)%4=(n*(n+1))%4 at eq
  rw [Nat.mul_mod n,Nat.add_mod n 1] at eq
  rw [Nat.even_iff]
  have hn4 := Nat.mod_lt n (by decide : 0<4)
  interval_cases n%4 <;> omega
private theorem foldEven (n : ℕ) (hn : 0<n) : folds n ↔ Even (total n) := by
  constructor
  · rintro ⟨i,j,_,_,e⟩
    exact ⟨total j-total i,by omega⟩
  · intro h
    obtain h|h := (par n).mp h
    · let k := n/4
      have e : n=4*k := by dsimp [k];omega
      refine ⟨k,3*k,by omega,by omega,?_⟩
      nlinarith [triangle n,triangle k,triangle (3*k),e]
    · let k := n/4
      have e : n=4*k+3 := by dsimp [k];omega
      refine ⟨k,3*k+2,by omega,by omega,?_⟩
      rw [e]
      nlinarith [triangle (4*k+3),triangle k,triangle (3*k+2)]
private theorem sqr (z : ℕ) : z^2%4=0 ∨ z^2%4=1 := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt z (by decide : 0<4)
  interval_cases z%4 <;> decide
private theorem index (n : ℕ) (hn : 0<n) : inA154708 n ↔ Even (total n) := by
  rw [par]
  constructor
  · rintro ⟨b,c,_,_,eq⟩
    have em := congrArg (fun x => x%4) eq
    change (n*(n+1)+b^2)%4=c^2%4 at em
    rw [Nat.add_mod,Nat.mul_mod,Nat.add_mod n 1] at em
    have sb := sqr b
    have sc := sqr c
    have hn4 := Nat.mod_lt n (by decide : 0<4)
    interval_cases n%4 <;> omega
  · rintro (h|h)
    · let k := n/4
      have e : n=4*k := by dsimp [k];omega
      refine ⟨3*k+1,5*k+1,by omega,by omega,?_⟩
      rw [e];ring
    · let k := n/4
      have e : n=4*k+3 := by dsimp [k];omega
      refine ⟨3*k+2,5*k+4,by omega,by omega,?_⟩
      rw [e];ring
theorem result : type_of% @OMA.S_oeis_a382605.main := by
  intro n hn
  exact ⟨foldEven n hn,(foldEven n hn).trans (index n hn).symm⟩
end Deldor14.EqualSides
theorem OMA.solution : type_of% @OMA.S_oeis_a382605.main := Deldor14.EqualSides.result
