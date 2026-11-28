import RothForcedHole
import Mathlib.Tactic

open Finset Erdos142LongDigits Erdos142RamseyGlue Erdos142ForcedHole
namespace Erdos142LocalObstruction

/-- The next-but-one uncovered interval starts beyond the end of the first,
    even when the set of allowable new points shrinks. -/
theorem alternate_disjoint {a b c L p q : ℕ} {U V : Finset ℕ} (shrinks : V⊆U)
    (best : ∀ z ∈ U, a≤z → z<a+L → z≤p) (afterP : p<b) (first : a≤p)
    (inNext : b≤q) (available : q∈V) (afterQ : q<c) : a+L≤c := by
  by_contra! h
  have := best q (shrinks available) (by omega) (by omega)
  omega

/-- Necessary congruences when two of the three completion locations
    occur in the same progression. Coordinates are relative to its residue. -/
theorem two_congruences {q x y : ℤ}
    (h : ((q ∣ 2*x-y) ∧ (q ∣ 2*y-x)) ∨ ((q ∣ 2*x-y) ∧ (q ∣ x+y)) ∨
      ((q ∣ 2*y-x) ∧ (q ∣ x+y))) : q ∣ x+y ∧ q ∣ 3*x ∧ q ∣ 3*y := by
  rcases h with ⟨⟨a,ha⟩,⟨b,hb⟩⟩|⟨⟨a,ha⟩,⟨b,hb⟩⟩|⟨⟨a,ha⟩,⟨b,hb⟩⟩
  · exact ⟨⟨a+b,by linear_combination ha+hb⟩,
      ⟨2*a+b,by linear_combination 2*ha+hb⟩,⟨a+2*b,by linear_combination ha+2*hb⟩⟩
  · exact ⟨⟨b,hb⟩,⟨a+b,by linear_combination ha+hb⟩,⟨2*b-a,by linear_combination 2*hb-ha⟩⟩
  · exact ⟨⟨b,hb⟩,⟨2*b-a,by linear_combination 2*hb-ha⟩,⟨a+b,by linear_combination ha+hb⟩⟩

theorem pair_capacity {f u v count : ℝ} (nonneg : 0≤u+v) (size : u+v≤f)
    (bound : 2*count≤f*(f-1)-u*(u-1)-v*(v-1)+4*u*v) : 4*count≤3*f^2 := by
  have mul := mul_nonneg (sub_nonneg.mpr size) (show 0≤f+(u+v) by linarith)
  nlinarith [sq_nonneg (u-v)]

private def center (m : ℕ) := 4^m-1

def pins (m : ℕ) :=
  (digits m).image (fun x => 3*(center m-x)+1) ∪
    (digits m).image (fun y => 3*center m+2+3*y)

private theorem digit_le_center {m x : ℕ} (hx : x∈digits m) : x≤center m := by
  have := digit_bound hx
  have := span m
  unfold center
  omega

theorem pins_count (m : ℕ) : (pins m).card=2*2^m := by
  rw [pins,card_union_of_disjoint]
  · rw [card_image_of_injOn (by
      intro x hx y hy e
      have := digit_le_center hx
      have := digit_le_center hy
      dsimp at e
      omega),card_image_of_injective _ (by intro x y e; dsimp at e; omega),digit_count]
    omega
  · apply disjoint_left.mpr
    intro z hx hy
    obtain ⟨x,_,ex⟩ := mem_image.mp hx
    obtain ⟨y,_,ey⟩ := mem_image.mp hy
    omega

private theorem split_pin {m x : ℕ} (hx : x∈pins m) :
    (∃ u ∈ digits m, x+3*u=3*center m+1) ∨ (∃ u ∈ digits m, x=3*center m+2+3*u) := by
  rcases mem_union.mp hx with h|h <;> obtain ⟨u,hu,rfl⟩ := mem_image.mp h
  · exact Or.inl ⟨u,hu,by have := digit_le_center hu; omega⟩
  · exact Or.inr ⟨u,hu,rfl⟩

theorem pins_fit {m x : ℕ} (hx : x∈pins m) : x<6*4^m := by
  rcases split_pin hx with ⟨u,hu,eq⟩|⟨u,hu,eq⟩ <;>
    have bound := digit_bound hu <;> have identity := span m <;> unfold center at eq <;> omega

theorem pins_free (m : ℕ) : Free 3 (pins m) := by
  intro a q hq terms
  have z : a ∈ pins m := by simpa using terms 0 (by decide)
  have o : a+q ∈ pins m := by simpa using terms 1 (by decide)
  rcases split_pin z with ⟨u,hu,eu⟩|⟨u,hu,eu⟩ <;>
    rcases split_pin o with ⟨v,hv,ev⟩|⟨v,hv,ev⟩ <;>
    rcases split_pin (terms 2 (by decide)) with ⟨w,hw,ew⟩|⟨w,hw,ew⟩
  all_goals first | omega | (have := digit_midpoint hu hv hw (by omega); omega)

private theorem forbid_after {A : Finset ℕ} (fr : Free 3 A) {x y z : ℕ}
    (hx : x∈A) (hy : y∈A) (small : x<y) (eq : x+z=2*y) : z∉A := by
  intro hz
  apply fr x (y-x) (by omega)
  intro i hi
  interval_cases i
  · simpa using hx
  · convert hy using 1
    omega
  · convert hz using 1
    omega

/-- Both endpoint completions are used, in adjacent halves of a step-three window. -/
theorem pins_hole {m : ℕ} {A : Finset ℕ} (inc : pins m ⊆ A) (fr : Free 3 A)
    {i : ℕ} (hi : i<2*4^m) : 3*i ∉ A := by
  have id := span m
  have cp : center m+1=4^m := by unfold center; omega
  have left (x : ℕ) (hx : x∈digits m) : 3*(center m-x)+1 ∈ A :=
    inc (mem_union_left _ (mem_image.mpr ⟨x,hx,rfl⟩))
  have right (y : ℕ) (hy : y∈digits m) : 3*center m+2+3*y ∈ A :=
    inc (mem_union_right _ (mem_image.mpr ⟨y,hy,rfl⟩))
  by_cases lower : i<4^m
  · obtain ⟨y,hy,x,hx,e⟩ := representation (m:=m) (t:=center m-i) (by omega)
    have xbound := digit_le_center hx
    have l := left x hx
    have r := right y hy
    intro h
    exact forbid_after fr h l (by omega) (by omega) r
  · obtain ⟨x,hx,y,hy,e⟩ := representation (m:=m) (t:=i-4^m) (by omega)
    have xbound := digit_le_center hx
    exact forbid_after fr (left x hx) (right y hy) (by omega) (by omega)

#print axioms alternate_disjoint
#print axioms two_congruences
#print axioms pair_capacity
#print axioms pins_count
#print axioms pins_fit
#print axioms pins_free
#print axioms pins_hole
end Erdos142LocalObstruction
