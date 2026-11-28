import RothDyadicClusters
import RothExactDefects

open Finset Erdos142ExactDefects
namespace Erdos142DyadicClusters

private theorem weak_of_covers {A B C D : Finset ℕ} {t : ℕ}
    (free : ThreeAPFree (↑A : Set ℕ)) (c : Covers A C t) (d : Covers A D (2*t))
    (sub : B ⊆ A) (missC : ∀ x ∈ B, x ∉ C) (missD : ∀ x ∈ B, x ∉ D) :
    Weak t B := by
  intro x hx y hy z hz eq
  by_contra! different
  obtain ⟨xy,yz,xz⟩ := different
  have no₁ : |(x:ℤ)+z-2*y| ≠ (t:ℤ) := by
    intro h
    rcases c x (sub hx) y (sub hy) z (sub hz) xy yz xz h with e|e|e
    · exact missC _ hx e
    · exact missC _ hy e
    · exact missC _ hz e
  have no₂ : |(x:ℤ)+z-2*y| ≠ ↑(2*t) := by
    intro h
    rcases d x (sub hx) y (sub hy) z (sub hz) xy yz xz h with e|e|e
    · exact missD _ hx e
    · exact missD _ hy e
    · exact missD _ hz e
  have no₀ : x+z ≠ y+y := fun h => xz (threeAPFree_iff_eq_right.mp free (sub hx) (sub hy) (sub hz) h)
  push_cast at no₂
  rw [abs_eq_max_neg] at no₁ no₂
  omega

private theorem cut_count (A U : Finset ℕ) : A.card ≤ (A \ U).card + U.card := by
  calc
    _ ≤ ((A \ U) ∪ U).card := card_le_card (by intro x hx; by_cases h : x ∈ U <;> simp [h,hx])
    _ ≤ _ := card_union_le _ _

/-- A small pair of covers forces many original pairs at distance t. -/
theorem paired_cover_bound (A C D : Finset ℕ) (n t : ℕ) (ht : 0<t)
    (fit : A ⊆ range n) (free : ThreeAPFree (↑A : Set ℕ))
    (c : Covers A C t) (d : Covers A D (2*t)) :
    4*A.card ≤ 3*rothNumberNat (n+t) + 2*(pairs t A).card + 4*(C.card+D.card) := by
  let B := A \ (C ∪ D)
  have sub : B ⊆ A := sdiff_subset
  have exc {x} (h : x ∈ B) : x ∉ C ∧ x ∉ D := by
    simpa using (mem_sdiff.mp h).2
  have weak := weak_of_covers free c d sub (fun _ h => (exc h).1) (fun _ h => (exc h).2)
  have gain := integer_gain B n t ht (fun _ h => fit (sub h)) weak
  have incl : pairs t B ⊆ pairs t A := fun _ h =>
    mem_filter.mpr ⟨sub (mem_filter.mp h).1, sub (mem_filter.mp h).2⟩
  have cp := card_le_card incl
  have bound : A.card ≤ B.card + (C ∪ D).card := cut_count _ _
  have u := card_union_le C D
  omega

/-- Every triple of covers on a dyadic chain pays for the uniform finite deficit. -/
theorem three_cover_bound (A C D E : Finset ℕ) (n t : ℕ) (ht : 0<t)
    (fit : A ⊆ range n) (free : ThreeAPFree (↑A : Set ℕ))
    (c : Covers A C t) (d : Covers A D (2*t)) (e : Covers A E (4*t)) :
    7*A.card ≤ 6*rothNumberNat (n+2*t) + 7*(C.card+D.card+E.card) := by
  let B := A \ (C ∪ D ∪ E)
  have sub : B ⊆ A := sdiff_subset
  have exc {x} (h : x ∈ B) : x ∉ C ∧ x ∉ D ∧ x ∉ E := by
    simpa [not_or,and_assoc] using (mem_sdiff.mp h).2
  have w1 := weak_of_covers free c d sub (fun _ h => (exc h).1) (fun _ h => (exc h).2.1)
  have e' : Covers A E (2*(2*t)) := by
    convert e using 1
    omega
  have w2 := weak_of_covers free d e' sub (fun _ h => (exc h).2.1) (fun _ h => (exc h).2.2)
  have gain := dyadic_defect_bound B n t ht (fun _ h => fit (sub h)) w1 w2
  have bound : A.card ≤ B.card + (C ∪ D ∪ E).card := cut_count _ _
  have u := card_union_le C D
  have v := card_union_le (C ∪ D) E
  omega

#print axioms paired_cover_bound
#print axioms three_cover_bound
end Erdos142DyadicClusters
