import OMAStatements.S_oeis_a343311
import Mathlib

open OMA.S_oeis_a343311

namespace Deldor14.DistinctTriples

theorem excluded {n : ℕ} (h : represented n) : n≠4 ∧ n≠8 ∧ n≠9 ∧ n≠25 := by
  obtain ⟨x,y,z,hx,hy,hz,xy,xz,yz,total,divides⟩ := h
  let ok (a b c : Fin 26) := 0<a.val ∧ 0<b.val ∧ 0<c.val ∧
    a≠b ∧ a≠c ∧ b≠c ∧ (a.val+b.val+c.val) ∣ a.val*b.val*c.val
  have finite : ∀ a b c : Fin 26, (a.val+b.val+c.val ∈ ([4,8,9,25] : List ℕ)) → ¬ok a b c := by
    decide +kernel
  have bad : n∈([4,8,9,25] : List ℕ) → False := by
    intro member
    have small : n≤25 := by simp at member; omega
    let a : Fin 26 := ⟨x,by omega⟩
    let b : Fin 26 := ⟨y,by omega⟩
    let c : Fin 26 := ⟨z,by omega⟩
    exact finite a b c (total ▸ member) ⟨hx,hy,hz,
      fun e => xy (congrArg Fin.val e),fun e => xz (congrArg Fin.val e),
      fun e => yz (congrArg Fin.val e),total ▸ divides⟩
  simpa using bad

theorem even_case (b : ℕ) (hb : 3≤b) (skip : b≠4) : represented (2*b) := by
  refine ⟨2,b,b-2,by omega,by omega,by omega,by omega,by omega,by omega,by omega,?_⟩
  exact dvd_mul_right _ _

theorem distinct_case {a b : ℕ} (ha : 3≤a) (order : a<b) : represented (a*b) := by
  have mul := Nat.mul_le_mul_right b ha
  have large : a+b+b < a*b := by omega
  let z := a*b-(a+b)
  have hz : b<z := by dsimp [z]; omega
  exact ⟨a,b,z,by omega,by omega,by omega,by omega,by omega,by omega,
    by dsimp [z]; omega,dvd_mul_right _ _⟩

theorem equal_case {p : ℕ} (hp : 6≤p) : represented (p*p) := by
  let z := p*p - 3*p
  have big := Nat.mul_le_mul_right p hp
  have hz : 2*p < z := by dsimp [z]; omega
  refine ⟨p,2*p,z,by omega,by omega,by omega,by omega,by omega,by omega,
    by dsimp [z]; omega,2*z,?_⟩
  ring

theorem ordered {a b : ℕ} (ha : 2≤a) (ordered : a≤b)
    (h4 : a*b≠4) (h8 : a*b≠8) (h9 : a*b≠9) (h25 : a*b≠25) :
    represented (a*b) := by
  by_cases two : a=2
  · subst a; exact even_case b (by omega) (by omega)
  by_cases equal : a=b
  · subst b
    by_cases four : a=4
    · subst a; exact even_case 8 (by decide) (by decide)
    have bound : 6≤a := by
      by_contra! smaller
      interval_cases a <;> omega
    exact equal_case bound
  exact distinct_case (by omega) (by omega)

end Deldor14.DistinctTriples
open Deldor14.DistinctTriples

theorem OMA.solution : type_of% @OMA.S_oeis_a343311.main := by
  intro n
  constructor
  · intro h
    obtain ⟨h4,h8,h9,h25⟩ := excluded h
    obtain ⟨x,y,z,hx,hy,hz,xy,xz,yz,total,divides⟩ := h
    refine ⟨by omega,?_,h4,h8,h9,h25⟩
    intro prime
    rcases prime.dvd_mul.mp divides with d | d
    · rcases prime.dvd_mul.mp d with dx | dy
      · have := Nat.le_of_dvd hx dx; omega
      · have := Nat.le_of_dvd hy dy; omega
    · have := Nat.le_of_dvd hz d; omega
  · rintro ⟨large,np,h4,h8,h9,h25⟩
    obtain ⟨a,b,ha,hb,prod⟩ := (Nat.not_prime_iff_exists_mul_eq large).mp np
    have aa : 2≤a := by
      by_contra! small; interval_cases a <;> simp_all
    have bb : 2≤b := by
      by_contra! small; interval_cases b <;> simp_all
    subst n
    rcases le_total a b with order | order
    · exact ordered aa order h4 h8 h9 h25
    · rw [Nat.mul_comm] at h4 h8 h9 h25 ⊢
      exact ordered bb order h4 h8 h9 h25
