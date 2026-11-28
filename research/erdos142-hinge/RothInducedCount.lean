import RothInducedTriples

open Finset
namespace Erdos142InducedTriples
open Erdos142DyadicClusters

noncomputable def freeSets (n : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (range n).powerset.filter (fun S => ThreeAPFree (↑S : Set ℕ))

private def digits : Fin 7 → Finset (Fin 3) :=
  ![∅, {0}, {1}, {2}, {0,1}, {0,2}, {1,2}]

private theorem different_digits : Function.Injective digits := by decide
private theorem local_free : ∀ w i j k, i ∈ digits w → j ∈ digits w →
    k ∈ digits w → i.val+k.val=j.val+j.val → i=k := by decide

/-- All seven proper subsets may be chosen independently at each root. -/
theorem seven_choices {A : Finset ℕ} {n t : ℕ} (ht : 0<t) (fit : A ⊆ range n)
    (weak : Weak t A) : 7^(pairs t A).card ≤ (freeSets (n+t)).card := by
  classical
  let Root := ↥(pairs t A)
  let site (p : Root × Fin 3) := expand t (p.1.val,p.2)
  have si : Function.Injective site := by
    rintro ⟨⟨x,hx⟩,i⟩ ⟨⟨y,hy⟩,j⟩ h
    have eq := ternary_faithful ht weak
      (mem_product.mpr ⟨hx,mem_univ i⟩) (mem_product.mpr ⟨hy,mem_univ j⟩) h
    cases eq
    rfl
  let select (f : Root → Fin 7) :=
    (univ.filter fun p : Root × Fin 3 => p.2 ∈ digits (f p.1)).image site
  have at_site (f : Root → Fin 7) (p : Root × Fin 3) :
      site p ∈ select f ↔ p.2 ∈ digits (f p.1) := by
    constructor
    · intro h
      obtain ⟨q,hq,e⟩ := mem_image.mp h
      obtain rfl := si e
      exact (mem_filter.mp hq).2
    · intro h
      exact mem_image.mpr ⟨p,mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩
  have diff : Function.Injective select := by
    intro f g eq
    funext x
    apply different_digits
    ext i
    rw [← at_site f (x,i),← at_site g (x,i),eq]
  have inside (f : Root → Fin 7) : select f ∈ freeSets (n+t) := by
    apply mem_filter.mpr
    constructor
    · apply mem_powerset.mpr
      intro y hy
      obtain ⟨⟨⟨x,hx⟩,i⟩,_,rfl⟩ := mem_image.mp hy
      have xt := mem_range.mp (fit (mem_filter.mp hx).2)
      change x+i.val*t ∈ range (n+t)
      have small := Nat.mul_le_mul_right t (show i.val≤2 by have := i.isLt; omega)
      rw [mem_range]
      omega
    · apply threeAPFree_iff_eq_right.mpr
      intro a ha b hb c hc e
      obtain ⟨⟨x,i⟩,xi,rfl⟩ := mem_image.mp ha
      obtain ⟨⟨y,j⟩,yj,rfl⟩ := mem_image.mp hb
      obtain ⟨⟨z,k⟩,zk,rfl⟩ := mem_image.mp hc
      obtain ⟨xy,yz,ij⟩ := ternary_projection ht weak x.property y.property z.property i j k e
      obtain rfl := Subtype.ext xy
      obtain rfl := Subtype.ext yz
      have same : i=k := local_free _ _ _ _ (mem_filter.mp xi).2 (mem_filter.mp yj).2 (mem_filter.mp zk).2 ij
      rw [same]
  have inc : univ.image select ⊆ freeSets (n+t) := by
    intro u hu
    obtain ⟨f,_,rfl⟩ := mem_image.mp hu
    exact inside f
  have count := card_le_card inc
  rw [card_image_of_injective _ diff] at count
  simpa [Root] using count

#print axioms seven_choices
end Erdos142InducedTriples
