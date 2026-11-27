import OMAStatements.S_oeis_a045798
import Mathlib

open OMA.S_oeis_a045798
namespace Deldor14.Oddish

def f (i : ℕ) := 20*(i/4)+11+2*(i%4)+2*((i%4)/2)

theorem classes (k : ℕ) :
    oddish k ↔ k%20=11 ∨ k%20=13 ∨ k%20=17 ∨ k%20=19 := by
  unfold oddish Nat.Coprime
  rw [Nat.gcd_comm k 10,Nat.gcd_rec 10 k]
  have hd : k%10=(k%20)%10 := by omega
  have ht : (k/10%10)%2=(k%20)/10 := by omega
  rw [hd,ht]
  have : k%20 < 20 := Nat.mod_lt _ (by decide)
  generalize k%20 = r at *
  interval_cases r <;> decide

theorem inClass (i : ℕ) : oddish (f i) := by
  rw [classes]
  unfold f
  have hr : i%4=0 ∨ i%4=1 ∨ i%4=2 ∨ i%4=3 := by omega
  rcases hr with h | h | h | h <;> rw [h] <;> omega

theorem onto (k : ℕ) (hk : oddish k) : k ∈ Set.range f := by
  rcases (classes k).mp hk with h | h | h | h
  · exact ⟨4*(k/20), by unfold f; omega⟩
  · exact ⟨4*(k/20)+1, by unfold f; omega⟩
  · exact ⟨4*(k/20)+2, by unfold f; omega⟩
  · exact ⟨4*(k/20)+3, by unfold f; omega⟩

theorem enumerates (i : ℕ) : Nat.nth oddish i = f i := by
  have mono : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro j; unfold f; omega
  have inf : (Set.ofPred oddish).Infinite :=
    (Set.infinite_range_of_injective mono.injective).mono (Set.range_subset_iff.mpr inClass)
  have h := Nat.nth_comp_of_strictMono (p:=oddish) (n:=i) mono onto (fun h => (inf h).elim)
  rw [Nat.nth_of_forall (fun j _ => inClass j)] at h
  exact h.symm

end Deldor14.Oddish
open Deldor14.Oddish

theorem OMA.solution : type_of% @OMA.S_oeis_a045798.main := by
  intro n hn
  simp only [a,enumerates,f]
  omega
