import RothRamseyGlue

open Finset Erdos142LongDigits Erdos142RamseyGlue
namespace Erdos142ForcedHole

def digits : ℕ → Finset ℕ
  | 0 => {0}
  | m+1 => (digits m).image (fun x => 4*x) ∪ (digits m).image (fun x => 4*x+1)

def top : ℕ → ℕ
  | 0 => 0
  | m+1 => 4*top m+1

theorem span (m : ℕ) : 3*top m+1=4^m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [top,pow_succ,←ih]; ring

private theorem unpack {m x : ℕ} (hx : x∈digits (m+1)) :
    ∃ a ∈ digits m, ∃ e ≤ 1, x=4*a+e := by
  rcases mem_union.mp hx with h|h
  · obtain ⟨a,ha,rfl⟩ := mem_image.mp h
    exact ⟨a,ha,0,by decide,by omega⟩
  · obtain ⟨a,ha,rfl⟩ := mem_image.mp h
    exact ⟨a,ha,1,by decide,rfl⟩

private theorem pack {m x e : ℕ} (hx : x∈digits m) (he : e≤1) :
    4*x+e ∈ digits (m+1) := by
  interval_cases e
  · exact mem_union_left _ (mem_image.mpr ⟨x,hx,rfl⟩)
  · exact mem_union_right _ (mem_image.mpr ⟨x,hx,rfl⟩)

theorem digit_bound {m x : ℕ} (mem : x∈digits m) : x≤top m := by
  induction m generalizing x with
  | zero => simpa [digits,top] using mem
  | succ m ih =>
    obtain ⟨a,ha,e,he,rfl⟩ := unpack mem
    have := ih ha
    rw [top]
    omega

theorem digit_midpoint {m x y z : ℕ}
    (hx : x∈digits m) (hy : y∈digits m) (hz : z∈digits m)
    (eq : x+z=2*y) : x=z := by
  induction m generalizing x y z with
  | zero => simp [digits] at hx hz; omega
  | succ m ih =>
    obtain ⟨a,ha,i,hi,rfl⟩ := unpack hx
    obtain ⟨b,hb,j,hj,rfl⟩ := unpack hy
    obtain ⟨c,hc,l,hl,rfl⟩ := unpack hz
    have := ih ha hb hc (by omega)
    omega

theorem digit_count (m : ℕ) : (digits m).card=2^m := by
  induction m with
  | zero => simp [digits]
  | succ m ih =>
    rw [digits,card_union_of_disjoint]
    · rw [card_image_of_injective _ (by intro a b e; dsimp at e; omega),
          card_image_of_injective _ (by intro a b e; dsimp at e; omega),ih,pow_succ]
      omega
    · apply disjoint_left.mpr
      intro x h1 h2
      obtain ⟨a,_,e⟩ := mem_image.mp h1
      obtain ⟨b,_,f⟩ := mem_image.mp h2
      omega

/-- Complementary binary positions in the base-four digits cover the whole interval. -/
theorem representation {m t : ℕ} (ht : t<4^m) :
    ∃ x ∈ digits m, ∃ y ∈ digits m, t=x+2*y := by
  induction m generalizing t with
  | zero =>
    refine ⟨0,by simp [digits],0,by simp [digits],?_⟩
    norm_num at ht
    omega
  | succ m ih =>
    rw [pow_succ] at ht
    obtain ⟨x,hx,y,hy,eq⟩ := ih (t:=t/4) (by omega)
    refine ⟨4*x+t%2,pack hx (by omega),4*y+(t%4)/2,pack hy (by omega),?_⟩
    omega

def obstruction (m : ℕ) :=
  (digits m).image (fun x => top m-x) ∪
  (digits m).image (fun y => 2*top m+1+y)

theorem obstruction_count (m : ℕ) : (obstruction m).card=2*2^m := by
  rw [obstruction,card_union_of_disjoint]
  · rw [card_image_of_injOn (by
      intro x hx y hy eq
      have := digit_bound hx
      have := digit_bound hy
      dsimp at eq
      omega),card_image_of_injective _ (by intro x y eq; dsimp at eq; omega),digit_count]
    omega
  · apply disjoint_left.mpr
    intro z hl hr
    obtain ⟨x,_,ex⟩ := mem_image.mp hl
    obtain ⟨y,_,ey⟩ := mem_image.mp hr
    omega

private theorem left_right {m x : ℕ} (hx : x∈obstruction m) :
    (∃ u∈digits m, x+u=top m) ∨ (∃ u∈digits m, x=2*top m+1+u) := by
  rcases mem_union.mp hx with h|h <;> obtain ⟨u,hu,rfl⟩ := mem_image.mp h
  · exact Or.inl ⟨u,hu,by have := digit_bound hu; omega⟩
  · exact Or.inr ⟨u,hu,rfl⟩

theorem obstruction_fit {m x : ℕ} (hx : x∈obstruction m) : x≤4^m := by
  have := span m
  rcases left_right hx with ⟨u,hu,e⟩|⟨u,hu,e⟩ <;> have := digit_bound hu <;> omega

theorem obstruction_free (m : ℕ) : Free 3 (obstruction m) := by
  intro a q pos terms
  have h0 : a ∈ obstruction m := by simpa using terms 0 (by decide)
  have h1 : a+q ∈ obstruction m := by simpa using terms 1 (by decide)
  have h2 := terms 2 (by decide)
  rcases left_right h0 with ⟨u,hu,e⟩|⟨u,hu,e⟩ <;>
    rcases left_right h1 with ⟨v,hv,f⟩|⟨v,hv,f⟩ <;>
    rcases left_right h2 with ⟨w,hw,g⟩|⟨w,hw,g⟩
  all_goals have ub := digit_bound hu
  all_goals have vb := digit_bound hv
  all_goals have wb := digit_bound hw
  all_goals first | omega | (have := digit_midpoint hu hv hw (by omega); omega)

/-- No free extension can contain even one point of the entire following block. -/
theorem forced_hole {m : ℕ} {A : Finset ℕ} (inc : obstruction m ⊆ A) (fr : Free 3 A)
    {t : ℕ} (ht : t<4^m) : 4^m+1+t ∉ A := by
  obtain ⟨x,hx,y,hy,rfl⟩ := representation ht
  let u := top m-x
  let v := 2*top m+1+y
  have bx := digit_bound hx
  have bu : u∈A := inc (mem_union_left _ (mem_image.mpr ⟨x,hx,rfl⟩))
  have bv : v∈A := inc (mem_union_right _ (mem_image.mpr ⟨y,hy,rfl⟩))
  have sn := span m
  have gap : u<v := by dsimp [u,v]; omega
  intro bz
  apply fr u (v-u) (by omega)
  intro i hi
  interval_cases i
  · simpa using bu
  · convert bv using 1
    omega
  · convert bz using 1
    dsimp [u,v]
    omega

/-- The prescribed configuration defeats the actual all-step hitting predicate. -/
theorem no_hitting_extension {m L N : ℕ} (len : L≤4^m) (room : 4^m+L+1≤N)
    (A : Finset ℕ) (inc : obstruction m ⊆ A) (fr : Free 3 A) : ¬Hits N L A := by
  intro hit
  obtain ⟨j,hj,mem⟩ := hit (4^m+1) 1 (by decide) (by intro i hi; omega)
  exact forced_hole inc fr (lt_of_lt_of_le hj len) (by simpa using mem)

#print axioms no_hitting_extension
#print axioms digit_count
#print axioms representation
#print axioms obstruction_count
#print axioms obstruction_free
#print axioms obstruction_fit
#print axioms forced_hole
end Erdos142ForcedHole
