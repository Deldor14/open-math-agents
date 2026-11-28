import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic

open Finset
namespace Erdos142Punctures

/-- Short translations hitting one specified site form a progression-free set. -/
theorem reflected_hits (A : Finset ℕ) (hA : ThreeAPFree (↑A : Set ℕ)) (w x : ℕ) :
    ((range w).filter (fun t => ∃ a ∈ A, a+t=x)).card ≤ rothNumberNat w := by
  let H := (range w).filter (fun t => ∃ a ∈ A, a+t=x)
  have free : ThreeAPFree (↑H : Set ℕ) := by
    apply threeAPFree_iff_eq_right.mpr
    intro i hi j hj k hk h
    obtain ⟨a,ha,ea⟩ := (mem_filter.mp hi).2
    obtain ⟨b,hb,eb⟩ := (mem_filter.mp hj).2
    obtain ⟨c,hc,ec⟩ := (mem_filter.mp hk).2
    have eq : a+c=b+b := by omega
    have ac : a=c := threeAPFree_iff_eq_right.mp hA ha hb hc eq
    omega
  apply free.le_rothNumberNat
  · intro t ht
    exact mem_range.mp (mem_filter.mp ht).1
  · rfl

/-- A translate simultaneously misses all forbidden sites below the product threshold. -/
theorem exists_clean_shift (A T : Finset ℕ) (hA : ThreeAPFree (↑A : Set ℕ))
    (w : ℕ) (small : T.card * rothNumberNat w < w) :
    ∃ t < w, ∀ a ∈ A, a+t ∉ T := by
  classical
  let H (x : ℕ) := (range w).filter (fun t => ∃ a ∈ A, a+t=x)
  by_contra! denied
  have cover : range w ⊆ T.biUnion H := by
    intro t ht
    obtain ⟨a, ha, hx⟩ := denied t (mem_range.mp ht)
    exact mem_biUnion.mpr ⟨a+t, hx, mem_filter.mpr ⟨ht,a,ha,rfl⟩⟩
  have bound : (T.biUnion H).card ≤ T.card * rothNumberNat w := calc
    _ ≤ ∑ x ∈ T, (H x).card := card_biUnion_le
    _ ≤ ∑ _x ∈ T, rothNumberNat w := sum_le_sum (fun x _ => reflected_hits A hA w x)
    _ = _ := by simp
  have hw := card_le_card cover
  rw [card_range] at hw
  omega

#print axioms reflected_hits
#print axioms exists_clean_shift
end Erdos142Punctures
