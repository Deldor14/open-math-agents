import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic

open Finset
namespace Erdos142Height

private lemma unpack (w a b c i j k : ℕ) (ha : a < w) (hb : b < w) (hc : c < w)
    (he : (a+2*w*i)+(c+2*w*k) = (b+2*w*j)+(b+2*w*j)) :
    i+k=j+j ∧ a+c=b+b := by
  have hi : i+k=j+j := by
    rcases lt_trichotomy (i+k) (j+j) with h|h|h
    · have hm := Nat.mul_le_mul_left (2*w) (Nat.succ_le_of_lt h)
      nlinarith
    · exact h
    · have hm := Nat.mul_le_mul_left (2*w) (Nat.succ_le_of_lt h)
      nlinarith
  exact ⟨hi, by nlinarith [congrArg (fun n : ℕ => (2*w)*n) hi]⟩

/-- Two digits in radix 2w, with no carry from the low digit in a midpoint equation. -/
theorem digit_product (w s : ℕ) : rothNumberNat w * rothNumberNat s ≤ rothNumberNat (2*w*s) := by
  obtain ⟨A,hA,hac,haf⟩ := rothNumberNat_spec w
  obtain ⟨B,hB,hbc,hbf⟩ := rothNumberNat_spec s
  let f : ℕ × ℕ → ℕ := fun u => u.1+2*w*u.2
  have lo {a : ℕ} (h : a ∈ A) : a < w := mem_range.mp (hA h)
  have hi {b : ℕ} (h : b ∈ B) : b < s := mem_range.mp (hB h)
  have inj : Set.InjOn f (A ×ˢ B : Finset _) := by
    rintro ⟨a,i⟩ h ⟨b,j⟩ h' he
    have hx := mem_product.mp h
    have hy := mem_product.mp h'
    change a+2*w*i = b+2*w*j at he
    obtain ⟨h1,h2⟩ := unpack w a b a i j i (lo hx.1) (lo hy.1) (lo hx.1) (by rw [he])
    congr 1 <;> omega
  have free : ThreeAPFree (↑((A ×ˢ B).image f) : Set ℕ) := by
    apply threeAPFree_iff_eq_right.mpr
    intro x hx y hy z hz he
    obtain ⟨⟨a,i⟩,ha,rfl⟩ := mem_image.mp hx
    obtain ⟨⟨b,j⟩,hb,rfl⟩ := mem_image.mp hy
    obtain ⟨⟨c,k⟩,hc,rfl⟩ := mem_image.mp hz
    obtain ⟨ha,hia⟩ := mem_product.mp ha
    obtain ⟨hb,hib⟩ := mem_product.mp hb
    obtain ⟨hc,hic⟩ := mem_product.mp hc
    obtain ⟨h1,h2⟩ := unpack w a b c i j k (lo ha) (lo hb) (lo hc) he
    have hu := threeAPFree_iff_eq_right.mp haf ha hb hc h2
    have hv := threeAPFree_iff_eq_right.mp hbf hia hib hic h1
    change a = c at hu
    change i = k at hv
    exact congrArg f (Prod.ext hu hv)
  apply free.le_rothNumberNat
  · intro x hx
    obtain ⟨⟨a,i⟩,h,rfl⟩ := mem_image.mp hx
    obtain ⟨ha,hi'⟩ := mem_product.mp h
    have lim := Nat.mul_le_mul_left (2*w) (Nat.succ_le_of_lt (hi hi'))
    change a+2*w*i < 2*w*s
    nlinarith [lo ha]
  · rw [card_image_of_injOn inj, card_product, hac, hbc]

/-- Finite incidence form of the translate-selection argument. -/
theorem overlap_sum {α : Type*} (U : Finset α) (w b : ℕ)
    (hit : ℕ → α → ℕ) (cap : ∀ u ∈ U, ∑ j ∈ range w, hit j u ≤ b) :
    ∑ j ∈ range w, ∑ u ∈ U, hit j u ≤ U.card*b := by
  rw [sum_comm]
  calc
    _ ≤ ∑ _u ∈ U, b := sum_le_sum cap
    _ = _ := by simp

#print axioms digit_product
#print axioms overlap_sum
end Erdos142Height
