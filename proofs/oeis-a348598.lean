import OMAStatements.S_oeis_a348598
import Mathlib

open OMA.S_oeis_a348598
namespace Deldor14.SquarePrimes

private theorem next37 : nextSquarePrime 17 37 := by
  refine ⟨⟨by norm_num,6,rfl⟩,by decide,?_⟩
  rintro t ⟨prime,k,rfl⟩ lower
  by_contra! small
  have hi : k ≤ 5 := by nlinarith
  interval_cases k <;> norm_num at *

/- If t=k²+1 is an earlier candidate, a prime modulus divides k-4 or k+4.
Thus its own square root is at most fourteen, and the two root bounds are small. -/
set_option maxRecDepth 8192 in
private theorem minimum (t r : ℕ) (h : qualifies 17 t r) : 42437 ≤ t := by
  rcases h with ⟨⟨pt,k,rfl⟩,ht,⟨pr,v,rfl⟩,hr,cong⟩
  by_contra! small
  have kcap : k < 206 := by nlinarith
  have klo : 4 < k := by nlinarith
  let r := v^2+1
  have factor : k^2+1-17=(k-4)*(k+4) := by
    have hk : k-4+4=k := by omega
    have z : k^2+1-17+17=k^2+1 := by omega
    nlinarith [congrArg (fun t : ℕ => t*t) hk]
  have congr : Nat.ModEq r (k^2+1) 17 := cong
  have divides : r ∣ (k-4)*(k+4) := by
    rw [← factor]
    exact (Nat.modEq_iff_dvd' ht.le).mp congr.symm
  have rcap : r ≤ k+4 := by
    rcases pr.dvd_mul.mp divides with left | right
    · have := Nat.le_of_dvd (by omega : 0<k-4) left
      omega
    · exact Nat.le_of_dvd (by omega) right
  have vcap : v < 15 := by dsimp [r] at rcap; nlinarith
  have possibilities : v=6 ∨ v=10 ∨ v=14 := by
    have check : ∀ w : Fin 15, 17 < (w:ℕ)^2+1 → Nat.Prime ((w:ℕ)^2+1) →
        (w:ℕ)=6 ∨ (w:ℕ)=10 ∨ (w:ℕ)=14 := by decide +kernel
    exact check ⟨v,vcap⟩ hr pr
  have tested : ∀ i : Fin 206, 17 < (i:ℕ)^2+1 →
      (((i:ℕ)^2+1)%37=17 ∨ ((i:ℕ)^2+1)%101=17 ∨ ((i:ℕ)^2+1)%197=17) →
      ¬Nat.Prime ((i:ℕ)^2+1) := by decide +kernel
  apply tested ⟨k,kcap⟩ ht _ pt
  rcases possibilities with rfl | rfl | rfl
  · exact Or.inl cong
  · exact Or.inr (Or.inl cong)
  · exact Or.inr (Or.inr cong)
end Deldor14.SquarePrimes

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a348598.main) := by
  intro hyp
  have witness : qualifies 17 42437 101 :=
    ⟨⟨by norm_num,206,rfl⟩,by decide,⟨by norm_num,10,rfl⟩,by decide,by decide⟩
  have eq := hyp 17 37 42437 101 ⟨by norm_num,4,rfl⟩
    Deldor14.SquarePrimes.next37 witness Deldor14.SquarePrimes.minimum
  omega
