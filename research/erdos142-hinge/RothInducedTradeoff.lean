import RothInducedScales
import RothInducedDoubling
import RothMaximal

open Finset
namespace Erdos142InducedTriples
open Erdos142DyadicClusters Erdos142ExactDefects

/-- Joint finite bounds for any two covers in the initial progression-free set. -/
theorem cover_tradeoff (A C D : Finset ℕ) (n t : ℕ) (ht : 0<t) (fit : A ⊆ range n)
    (free : ThreeAPFree (↑A : Set ℕ)) (hc : Covers A C t) (hd : Covers A D (2*t)) :
    ∃ p : ℕ,
      4*A.card ≤ 3*rothNumberNat (n+t)+2*p+4*(C.card+D.card) ∧
      7^p ≤ (freeSets (n+t)).card ∧ 3^p ≤ (maximalFree (n+t)).card ∧
      4*p ≤ rothNumberNat (2*n+2*t) ∧
      ∀ b : ℕ, 0<b → ¬ b ∣ t → 3*p ≤ b*rothNumberNat ((n+t+b-1)/b) := by
  let B := A \ (C ∪ D)
  have sub : B ⊆ A := sdiff_subset
  have info {x} (h : x ∈ B) : x ∈ A ∧ x ∉ C ∧ x ∉ D := by simpa [B,not_or] using h
  have weak : Weak t B := by
    intro x hx y hy z hz eq
    by_contra! ne
    obtain ⟨xy,yz,xz⟩ := ne
    obtain ⟨ax,cx,dx⟩ := info hx
    obtain ⟨ay,cy,dy⟩ := info hy
    obtain ⟨az,cz,dz⟩ := info hz
    have w0 : x+z≠y+y := fun h => xz (threeAPFree_iff_eq_right.mp free ax ay az h)
    have w1 : |(x:ℤ)+z-2*y|≠(t:ℤ) := by
      intro e
      rcases hc x ax y ay z az xy yz xz e with h|h|h
      · exact cx h
      · exact cy h
      · exact cz h
    have w2 : |(x:ℤ)+z-2*y|≠↑(2*t) := by
      intro e
      rcases hd x ax y ay z az xy yz xz e with h|h|h
      · exact dx h
      · exact dy h
      · exact dz h
    push_cast at w2
    rw [abs_eq_max_neg] at w1 w2
    omega
  have loc : B ⊆ range n := fun _ h => fit (sub h)
  have cB : A.card ≤ B.card + (C ∪ D).card := by
    calc
      _ ≤ (B ∪ (C ∪ D)).card := card_le_card (by
        intro x h; by_cases u : x ∈ C ∪ D
        · exact mem_union_right _ u
        · exact mem_union_left _ (mem_sdiff.mpr ⟨h,u⟩))
      _ ≤ _ := card_union_le _ _
  have gain := integer_gain B n t ht loc weak
  have c := card_union_le C D
  exact ⟨(pairs t B).card,by omega,seven_choices ht loc weak,maximal_from_pairs ht loc weak,
    four_per_pair ht loc weak,fun _ hb h => residue_bound ht hb h loc weak⟩

#print axioms cover_tradeoff
end Erdos142InducedTriples
