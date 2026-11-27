import OMAStatements.S_oeis_a051064
import Mathlib

open Nat OMA.S_oeis_a051064
namespace Deldor14.Fibonacci

theorem period (n : ℕ) : fib (n+24) ≡ fib n [MOD 9] ∧ fib (n+24+1) ≡ fib (n+1) [MOD 9] := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    constructor
    · simpa only [show n+1+24=n+24+1 by omega] using ih.2
    · rw [show n+1+24+1=(n+24)+2 by omega,Nat.fib_add_two,Nat.fib_add_two (n:=n)]
      exact ih.1.add ih.2

theorem reduce (n : ℕ) : fib n ≡ fib (n%24) [MOD 9] := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : n<24
    · rw [Nat.mod_eq_of_lt hs]
    · have p := ((period (n-24)).1).trans (ih (n-24) (by omega))
      rwa [Nat.sub_add_cancel (by omega),show (n-24)%24=n%24 by omega] at p

theorem residues (n : ℕ) : (3∣fib n ↔ 4∣n) ∧ (9∣fib n ↔ 12∣n) := by
  have table : ∀ r : Fin 24, (3∣fib r ↔ 4∣r.val) ∧ (9∣fib r ↔ 12∣r.val) := by decide +kernel
  have row := table ⟨n%24,Nat.mod_lt _ (by decide)⟩
  have congr := reduce n
  change fib n %9 = fib (n%24)%9 at congr
  change (3∣fib (n%24) ↔ 4∣n%24) ∧ (9∣fib (n%24) ↔ 12∣n%24) at row
  omega

theorem triple (s : ℕ) :
    fib (3*(s+1)) = fib (s+1)*(3*fib s^2+3*fib s*fib (s+1)+2*fib (s+1)^2) := by
  rw [show 3*(s+1)=2*(s+1)+s+1 by omega,Nat.fib_add,Nat.fib_two_mul,Nat.fib_two_mul_add_one]
  rw [show s+1+1=s+2 by omega,Nat.fib_add_two]
  rw [show 2*(fib s+fib (s+1))-fib (s+1)=2*fib s+fib (s+1) by omega]
  ring

theorem oneVal (u : ℕ) (hu : 0<u) (three : 3∣u) (nine : ¬9∣u) : padicValNat 3 u=1 := by
  have h1 := (pow_dvd_iff_le_padicValNat (k:=1) (by decide : 3≠1) hu.ne').mp (by simpa using three)
  have h2 : ¬2≤padicValNat 3 u := fun h => nine ((pow_dvd_iff_le_padicValNat (by decide : 3≠1) hu.ne').mpr h)
  omega

theorem lift (n : ℕ) (hn : 0<n) (div : 4∣n) :
    padicValNat 3 (fib (3*n)) = padicValNat 3 (fib n)+1 := by
  obtain ⟨s,rfl⟩ : ∃ s, n=s+1 := ⟨n-1,by omega⟩
  have x := (residues (s+1)).1.mpr div
  have b : ¬3∣fib s := fun h => by have := (residues s).1.mp h; omega
  obtain ⟨u,hu⟩ := x
  let g := 3*fib s^2+3*fib s*fib (s+1)+2*fib (s+1)^2
  have fact : g=3*(fib s^2+3*fib s*u+6*u^2) := by unfold g; rw [hu]; ring
  have bn : fib s %3=1 ∨ fib s %3=2 := by omega
  have non : ¬3∣fib s^2+3*fib s*u+6*u^2 := by
    intro h
    have z := Nat.mod_eq_zero_of_dvd h
    simp only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.reduceMod, zero_mul,
      Nat.zero_mod, zero_add, add_zero, Nat.mod_mod] at z
    rcases bn with v | v <;> rw [v] at z <;> norm_num at z
  have gf : 0<g := by unfold g; have := Nat.fib_pos.mpr (show 0<s+1 by omega); positivity
  have vg := oneVal g gf (by rw [fact]; exact dvd_mul_right _ _) (by rw [fact]; omega)
  rw [triple, padicValNat.mul (Nat.fib_pos.mpr (by omega)).ne' gf.ne',vg]

end Deldor14.Fibonacci
open Deldor14.Fibonacci

theorem OMA.solution : type_of% @OMA.S_oeis_a051064.main := by
  constructor
  · intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases d : 3∣n
      · obtain ⟨t,ht⟩ := d
        have pos : 0<t := by omega
        have old := ih t (by omega) pos
        unfold a at old ⊢
        rw [ht, show 4*(3*t)=3*(4*t) by ring,lift _ (by omega) (dvd_mul_right _ _)]
        rw [padicValNat.mul (by decide : 3≠0) (by omega : 3*t≠0),padicValNat.self (by decide : 1<3)]
        omega
      · have a1 := (residues (4*n)).1.mpr (dvd_mul_right _ _)
        have a2 : ¬9∣fib (4*n) := fun h => by have := (residues (4*n)).2.mp h; omega
        rw [oneVal _ (Nat.fib_pos.mpr (by omega)) a1 a2]
        unfold a
        rw [padicValNat.mul (by decide : 3≠0) (by omega),padicValNat.self (by decide : 1<3),
          padicValNat.eq_zero_of_not_dvd d,add_zero]
  · intro n r h1 h3
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    have := (residues (4*n+r)).1.mp h
    omega
