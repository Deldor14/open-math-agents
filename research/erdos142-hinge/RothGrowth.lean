import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic

open Finset
namespace Erdos142Growth

/-- Separate two arbitrary optimal sets by the shortest universal gap between
    two intervals of these lengths. Coordinates in the first interval start at zero. -/
theorem glue (a b n : ℕ) (hb : 0 < b) (hba : b ≤ a) (hn : 2*a+b ≤ n+1) :
    rothNumberNat a + rothNumberNat b ≤ rothNumberNat n := by
  obtain ⟨A,hA,ca,fa⟩ := rothNumberNat_spec a
  obtain ⟨B,hB,cb,fb⟩ := rothNumberNat_spec b
  let s := 2*a-1
  let lift : ℕ → ℕ := fun x => s+x
  let U := A ∪ B.image lift
  have boundA {x} (h : x ∈ A) : x < a := mem_range.mp (hA h)
  have boundB {x} (h : x ∈ B) : x < b := mem_range.mp (hB h)
  have hs : s+1=2*a := by dsimp [s]; omega
  have separate : Disjoint A (B.image lift) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hy
    have := boundA hx
    dsimp [lift] at *
    omega
  have free : ThreeAPFree (↑U : Set ℕ) := by
    apply threeAPFree_iff_eq_right.mpr
    intro x hx y hy z hz eq
    have tag {v} (h : v ∈ U) : v ∈ A ∨ ∃ t ∈ B, v=s+t := by
      rcases mem_union.mp h with h|h
      · exact Or.inl h
      · obtain ⟨t,ht,rfl⟩ := mem_image.mp h
        exact Or.inr ⟨t,ht,rfl⟩
    rcases tag hx with x0|⟨u,hu,rfl⟩ <;>
      rcases tag hy with y0|⟨v,hv,rfl⟩ <;>
      rcases tag hz with z0|⟨w,hw,rfl⟩
    all_goals try exact threeAPFree_iff_eq_right.mp fa x0 y0 z0 eq
    all_goals try
      have mid : u+w=v+v := by omega
      have uw := threeAPFree_iff_eq_right.mp fb hu hv hw mid
      omega
    all_goals
      first | have bx := boundA x0 | have bx := boundB hu
      first | have by' := boundA y0 | have by' := boundB hv
      first | have bz := boundA z0 | have bz := boundB hw
      omega
  apply free.le_rothNumberNat
  · intro x hx
    rcases mem_union.mp hx with h|h
    · have := boundA h; omega
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp h
      have := boundB hy
      dsimp [lift]; omega
  · dsimp [U]
    rw [card_union_of_disjoint separate, card_image_of_injective _ (show Function.Injective lift by
      intro x y h; dsimp [lift] at h; omega), ca, cb]

/-- The doubling certificate uses eight finite interval inequalities. -/
theorem doubling (n : ℕ) (hn : 12 ≤ n) :
    7 * rothNumberNat n ≤ 6 * rothNumberNat (2*n) := by
  let c := (n+1)/3
  let a := c/2
  let b := (3*a-1)/2
  let d := 3*a-1
  have H (i j : ℕ) (h : i+j=n) : rothNumberNat n ≤ rothNumberNat i+rothNumberNat j := by
    rw [← h]; exact rothNumberNat_add_le i j
  have r1 := glue a a d (by dsimp [a,c]; omega) (le_refl _) (by dsimp [d]; omega)
  have r2 := glue b a (n-c) (by dsimp [a,c]; omega) (by dsimp [a,b,c]; omega)
    (by dsimp [a,b,c]; omega)
  have r3 := H (n-c) c (by dsimp [c]; omega)
  have r4 := glue (n-c) (n-c) (2*n) (by dsimp [c]; omega) (le_refl _) (by dsimp [c]; omega)
  have r5 := H (n-b) b (by dsimp [a,b,c]; omega)
  have r6 := glue (n-b) d (2*n) (by dsimp [a,c,d]; omega)
    (by dsimp [a,b,c,d]; omega) (by dsimp [a,b,c,d]; omega)
  have r7 := H (n-a) a (by dsimp [a,c]; omega)
  have r8 := glue (n-a) c (2*n) (by dsimp [a,c]; omega)
    (by dsimp [a,c]; omega) (by dsimp [a,c]; omega)
  omega

#print axioms glue
#print axioms doubling
end Erdos142Growth
