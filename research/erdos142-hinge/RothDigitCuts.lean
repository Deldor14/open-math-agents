import RothHeight

open Finset
namespace Erdos142DigitCuts

/-- At a radix cut, the support is a union of K products. Low digits have
    range w. Empty products and overlaps are allowed. -/
def Cover (A : Finset ℕ) (w K : ℕ) : Prop :=
  ∃ U V : Fin K → Finset ℕ, (∀ i, U i ⊆ range w) ∧
    ∀ x, x ∈ A ↔ ∃ i u, u ∈ U i ∧ ∃ v, v ∈ V i ∧ x = u+w*v

def slice (A : Finset ℕ) (w u : ℕ) :=
  (A.filter (fun x => x%w=u)).image (fun x => x/w)

theorem mem_slice {A : Finset ℕ} {w u v : ℕ} (hu : u<w) :
    v ∈ slice A w u ↔ u+w*v ∈ A := by
  constructor
  · intro h
    obtain ⟨x,hx,rfl⟩ := mem_image.mp h
    obtain ⟨xa,rem⟩ := mem_filter.mp hx
    rwa [← rem,Nat.mod_add_div]
  · intro h
    refine mem_image.mpr ⟨u+w*v,mem_filter.mpr ⟨h,?_⟩,?_⟩
    · simp [Nat.mod_eq_of_lt hu]
    · rw [Nat.mul_comm w v,Nat.add_mul_div_right _ _ (by omega : 0<w),Nat.div_eq_of_lt hu,zero_add]

theorem free_slice {A : Finset ℕ} {w u : ℕ} (hu : u<w)
    (free : ThreeAPFree (↑A : Set ℕ)) : ThreeAPFree (↑(slice A w u) : Set ℕ) := by
  apply threeAPFree_iff_eq_right.mpr
  intro x hx y hy z hz e
  have eq := congrArg (fun t : ℕ => w*t) e
  change w*(x+z)=w*(y+y) at eq
  rw [Nat.mul_add,Nat.mul_add] at eq
  have r := threeAPFree_iff_eq_right.mp free ((mem_slice hu).1 hx) ((mem_slice hu).1 hy)
      ((mem_slice hu).1 hz) (by omega)
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0<w) (Nat.add_left_cancel r)

theorem slice_range {A : Finset ℕ} {w u m : ℕ} (hu : u<w)
    (loc : A ⊆ range (w*m)) : slice A w u ⊆ range m := by
  intro v hv
  have cap := mem_range.mp (loc ((mem_slice hu).1 hv))
  exact mem_range.mpr (Nat.lt_of_mul_lt_mul_left (by omega : w*v<w*m))

/-- Fixing a low digit preserves the size of a cover at every higher cut. -/
theorem restrict_cover {A : Finset ℕ} {w u s K : ℕ} (hu : u<w)
    (cover : Cover A (w*s) K) : Cover (slice A w u) s K := by
  obtain ⟨U,V,fit,spec⟩ := cover
  refine ⟨fun i => slice (U i) w u,V,fun i => slice_range hu (fit i),?_⟩
  intro x
  rw [mem_slice hu,spec]
  constructor
  · rintro ⟨i,a,ha,v,hv,e⟩
    have rem := congrArg (fun z : ℕ => z%w) e
    change (u+w*x)%w=(a+w*s*v)%w at rem
    rw [Nat.mul_assoc] at rem
    simp [Nat.mod_eq_of_lt hu] at rem
    have ad := Nat.mod_add_div a w
    rw [← rem] at ad
    refine ⟨i,a/w,(mem_slice hu).2 (by simpa only [ad] using ha),v,hv,?_⟩
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0<w)
    rw [Nat.mul_add]
    nlinarith only [ad,e]
  · rintro ⟨i,a,ha,v,hv,rfl⟩
    exact ⟨i,u+w*a,(mem_slice hu).1 ha,v,hv,by ring⟩

/-- Peel one block. Each nonempty rectangle has a free low projection
    and its high projection fits inside a single honest slice of A. -/
theorem peel {A : Finset ℕ} {w K M : ℕ} (cover : Cover A w K)
    (free : ThreeAPFree (↑A : Set ℕ)) (cap : ∀ u<w, (slice A w u).card≤M) :
    A.card≤K*rothNumberNat w*M := by
  classical
  obtain ⟨U,V,fit,spec⟩ := cover
  let bin (i : Fin K) := (U i ×ˢ V i).image (fun p => p.1+w*p.2)
  have inA (i : Fin K) {u v} (hu : u ∈ U i) (hv : v ∈ V i) : u+w*v ∈ A :=
    (spec _).2 ⟨i,u,hu,v,hv,rfl⟩
  have each (i : Fin K) : (bin i).card≤rothNumberNat w*M := by
    by_cases a : (U i).Nonempty
    · by_cases b : (V i).Nonempty
      · obtain ⟨u,hu⟩ := a
        obtain ⟨v,hv⟩ := b
        have fu : ThreeAPFree (↑(U i) : Set ℕ) := by
          apply threeAPFree_iff_eq_right.mpr
          intro x hx y hy z hz e
          have r := threeAPFree_iff_eq_right.mp free (inA i hx hv) (inA i hy hv) (inA i hz hv) (by omega)
          exact Nat.add_right_cancel r
        have small := fu.le_rothNumberNat (U i) (fun z h => mem_range.mp (fit i h)) rfl
        have vs : V i ⊆ slice A w u := fun _ h => (mem_slice (mem_range.mp (fit i hu))).2 (inA i hu h)
        have big := (card_le_card vs).trans (cap u (mem_range.mp (fit i hu)))
        exact card_image_le.trans (by rw [card_product]; exact Nat.mul_le_mul small big)
      · simp [bin,not_nonempty_iff_eq_empty.mp b]
    · simp [bin,not_nonempty_iff_eq_empty.mp a]
  have sub : A ⊆ univ.biUnion bin := by
    intro x hx
    obtain ⟨i,u,hu,v,hv,rfl⟩ := (spec _).1 hx
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨(u,v),mem_product.mpr ⟨hu,hv⟩,rfl⟩⟩
  calc
    A.card ≤ (univ.biUnion bin).card := card_le_card sub
    _ ≤ ∑ i : Fin K, (bin i).card := card_biUnion_le
    _ ≤ ∑ _ : Fin K, rothNumberNat w*M := sum_le_sum (fun i _ => each i)
    _ = _ := by simp [Nat.mul_assoc]

/-- Read radices from the least significant end. Each pair specifies the
    next radix and an independent cover at the corresponding cut. -/
def Gates (A : Finset ℕ) (low : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | (w,K)::xs => Cover A (low*w) K ∧ Gates A (low*w) xs

private theorem restrict_gates {A : Finset ℕ} {w u : ℕ} (hu : u<w)
    (xs : List (ℕ × ℕ)) (low : ℕ) (g : Gates A (w*low) xs) : Gates (slice A w u) low xs := by
  induction xs generalizing low with
  | nil => trivial
  | cons pair xs ih =>
    obtain ⟨v,K⟩ := pair
    obtain ⟨c,tail⟩ := g
    rw [Nat.mul_assoc] at c tail
    exact ⟨restrict_cover hu c,ih _ tail⟩

theorem multicut (xs : List (ℕ × ℕ)) (q : ℕ) (A : Finset ℕ)
    (pos : ∀ pair ∈ xs, 0<pair.1)
    (fit : A ⊆ range ((xs.map Prod.fst).prod*q)) (free : ThreeAPFree (↑A : Set ℕ))
    (g : Gates A 1 xs) :
    A.card ≤ (xs.map (fun pair => pair.2*rothNumberNat pair.1)).prod*rothNumberNat q := by
  induction xs generalizing A with
  | nil =>
    simp only [List.map_nil,List.prod_nil,one_mul] at fit ⊢
    exact free.le_rothNumberNat A (fun x h => mem_range.mp (fit h)) rfl
  | cons pair xs ih =>
    obtain ⟨w,K⟩ := pair
    obtain ⟨cover,tail⟩ := g
    rw [one_mul] at cover tail
    simp only [List.map_cons,List.prod_cons] at fit ⊢
    rw [Nat.mul_assoc] at fit ⊢
    apply peel cover free
    intro u hu
    exact ih _ (fun p hp => pos p (List.mem_cons_of_mem _ hp)) (slice_range hu fit)
      (free_slice hu free) (restrict_gates hu xs 1 (by simpa using tail))

#print axioms restrict_cover
#print axioms peel
#print axioms multicut
end Erdos142DigitCuts
