import RothInducedCount

open Finset
namespace Erdos142InducedTriples
open Erdos142DyadicClusters

noncomputable def maximalFree (n : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (freeSets n).filter (fun S => ∀ T ∈ freeSets n, S ⊆ T → T=S)

private theorem extension {S : Finset ℕ} {n : ℕ} (h : S ∈ freeSets n) :
    ∃ T ∈ maximalFree n, S ⊆ T := by
  classical
  let pool := (freeSets n).filter (fun T => S ⊆ T)
  obtain ⟨T,ht,best⟩ := exists_max_image pool Finset.card
    (show pool.Nonempty from ⟨S,mem_filter.mpr ⟨h,Subset.rfl⟩⟩)
  obtain ⟨freeT,st⟩ := mem_filter.mp ht
  refine ⟨T,mem_filter.mpr ⟨freeT,?_⟩,st⟩
  intro V hv tv
  exact (eq_of_subset_of_card_le tv (best V (mem_filter.mpr ⟨hv,st.trans tv⟩))).symm

/-- A disjoint collection of isolated three-term progressions certifies
    at least three different maximal extensions per progression, multiplicatively. -/
theorem maximal_from_triples {ι : Type*} [Fintype ι] (n : ℕ) (site : ι → Fin 3 → ℕ)
    (fit : ∀ u i, site u i<n)
    (row : ∀ u, site u 0+site u 2=site u 1+site u 1)
    (ends : ∀ u, site u 0≠site u 2)
    (proj : ∀ x y z i j k, site x i+site z k=site y j+site y j →
      x=y ∧ y=z ∧ i.val+k.val=j.val+j.val) :
    3^Fintype.card ι ≤ (maximalFree n).card := by
  classical
  let S (f : ι → Fin 3) := (range n).filter (fun v => ∃ u i, i≠f u ∧ v=site u i)
  have ins {f : ι → Fin 3} {u i} (h : i≠f u) : site u i ∈ S f :=
    mem_filter.mpr ⟨mem_range.mpr (fit u i),u,i,h,rfl⟩
  have freeS (f : ι → Fin 3) : S f ∈ freeSets n := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (filter_subset _ _),threeAPFree_iff_eq_right.mpr ?_⟩
    intro X hx Y hy Z hz e
    obtain ⟨x,i,hi,rfl⟩ := (mem_filter.mp hx).2
    obtain ⟨y,j,hj,rfl⟩ := (mem_filter.mp hy).2
    obtain ⟨z,k,hk,rfl⟩ := (mem_filter.mp hz).2
    obtain ⟨rfl,rfl,d⟩ := proj _ _ _ _ _ _ e
    have small : ∀ (a i j k : Fin 3), i≠a → j≠a → k≠a →
        i.val+k.val=j.val+j.val → i=k := by decide
    rw [small (f x) _ _ _ hi hj hk d]
  choose full memfull contains using fun f => extension (freeS f)
  have inj : Function.Injective full := by
    intro f g eq
    funext u
    by_contra diff
    have all (i : Fin 3) : site u i ∈ full f := by
      by_cases cf : i=f u
      · rw [eq]
        exact contains g (ins (by simpa [cf] using diff : i≠g u))
      · exact contains f (ins cf)
    have fr : ThreeAPFree (↑(full f) : Set ℕ) := (mem_filter.mp (mem_filter.mp (memfull f)).1).2
    exact ends u (threeAPFree_iff_eq_right.mp fr (all 0) (all 1) (all 2) (row u))
  have cap := card_le_card (show univ.image full ⊆ maximalFree n by
    intro x hx
    obtain ⟨f,_,rfl⟩ := mem_image.mp hx
    exact memfull f)
  rw [card_image_of_injective _ inj] at cap
  simpa using cap

theorem maximal_from_pairs {A : Finset ℕ} {n t : ℕ} (ht : 0<t) (fit : A ⊆ range n)
    (weak : Weak t A) : 3^(pairs t A).card ≤ (maximalFree (n+t)).card := by
  let site (x : ↥(pairs t A)) (i : Fin 3) := x.val+i.val*t
  have cap := maximal_from_triples (n+t) site
    (by
      intro x i
      change x.val+i.val*t<n+t
      have sm := Nat.mul_le_mul_right t (show i.val≤2 by have := i.isLt; omega)
      have := mem_range.mp (fit (mem_filter.mp x.property).2)
      omega)
    (by intro x; simp [site]; omega)
    (by intro x; simp [site]; omega)
    (by
      intro x y z i j k eq
      obtain ⟨a,b,d⟩ := ternary_projection ht weak x.property y.property z.property i j k eq
      exact ⟨Subtype.ext a,Subtype.ext b,d⟩)
  simpa using cap

/-- An unconditional all-length lower bound for inclusion-maximal free sets. -/
theorem maximal_interval_lower (n : ℕ) :
    3^(rothNumberNat (n/5)) ≤ (maximalFree n).card := by
  obtain ⟨B,hB,size,free⟩ := rothNumberNat_spec (n/5)
  let site (x : ↥B) (i : Fin 3) := 5*x.val+i.val
  have cap := maximal_from_triples n site
    (by
      intro x i
      have h := mem_range.mp (hB x.property)
      have := i.isLt
      dsimp only [site]
      omega)
    (by intro x; simp [site]; omega)
    (by intro x; simp [site])
    (by
      intro x y z i j k eq
      dsimp only [site] at eq
      have := i.isLt
      have := j.isLt
      have := k.isLt
      have q : x.val+z.val=y.val+y.val := by omega
      have same := threeAPFree_iff_eq_right.mp free x.property y.property z.property q
      exact ⟨Subtype.ext (by omega),Subtype.ext (by omega),by omega⟩)
  simpa [size] using cap

#print axioms maximal_from_triples
#print axioms maximal_from_pairs
#print axioms maximal_interval_lower
end Erdos142InducedTriples
