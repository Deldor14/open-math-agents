import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic

open Finset

namespace Erdos142Defects

/-- Divide a residue class modulo t/2 by t/2 when t is even. A point between
    two positions that would create a repeated-coordinate obstruction yields
    a genuine three-point witness with an even signed defect. -/
theorem even_thinning_witness (a b c s : ℤ) (hab : a < b) (hbc : b < c)
    (close : ((c-a)%2=0 ∧ c-a ≤ 4*s) ∨ c-a ≤ 2*s) :
    ∃ k : ℤ, (k=a+c-2*b ∨ k=a+b-2*c ∨ k=b+c-2*a) ∧
      k%2=0 ∧ |k| ≤ 4*s := by
  by_cases he : (c-a)%2=0
  · refine ⟨a+c-2*b, Or.inl rfl, ?_, abs_le.mpr ?_⟩ <;> omega
  · by_cases hp : (a+b)%2=0
    · refine ⟨a+b-2*c, Or.inr (Or.inl rfl), ?_, abs_le.mpr ?_⟩ <;> omega
    · refine ⟨b+c-2*a, Or.inr (Or.inr rfl), ?_, abs_le.mpr ?_⟩ <;> omega

/-- A set avoiding all small signed multiples of a step, including those
    arising from repeated coordinates, admits an injective progression-free
    sum with a scaled optimal digit set. -/
theorem expansion_bound (B : Finset ℕ) (n s t : ℕ) (hB : B ⊆ range n)
    (strong : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, ∀ d : ℤ, |d| ≤ 2*(s:ℤ) →
      (x:ℤ)+z-2*y=d*(t:ℤ) → x=z ∧ d=0) :
    B.card * rothNumberNat (s+1) ≤ rothNumberNat (n+s*t) := by
  obtain ⟨D, hD, cD, freeD⟩ := rothNumberNat_spec (s+1)
  let lift : ℕ × ℕ → ℕ := fun p => p.1 + p.2*t
  let U := (B ×ˢ D).image lift
  have small {v} (h : v ∈ D) : v ≤ s := by
    have := mem_range.mp (hD h)
    omega
  have inj : Set.InjOn lift (↑(B ×ˢ D) : Set (ℕ × ℕ)) := by
    rintro ⟨x,u⟩ hx ⟨y,v⟩ hy heq
    obtain ⟨hx, hu⟩ := mem_product.mp hx
    obtain ⟨hy, hv⟩ := mem_product.mp hy
    change x+u*t=y+v*t at heq
    have hi : (x:ℤ)+(u:ℤ)*t=y+(v:ℤ)*t := by exact_mod_cast heq
    have hu' : (u:ℤ) ≤ s := by exact_mod_cast small hu
    have hv' : (v:ℤ) ≤ s := by exact_mod_cast small hv
    have h := strong x hx y hy y hy ((v:ℤ)-u) (abs_le.mpr (by omega))
      (by linarith [hi] : (x:ℤ)+y-2*y=((v:ℤ)-u)*t)
    exact Prod.ext h.1 (by omega)
  have free : ThreeAPFree (↑U : Set ℕ) := by
    apply threeAPFree_iff_eq_right.mpr
    intro a ha b hb c hc heq
    obtain ⟨⟨x,u⟩, hxu, rfl⟩ := mem_image.mp ha
    obtain ⟨⟨y,v⟩, hyv, rfl⟩ := mem_image.mp hb
    obtain ⟨⟨z,w⟩, hzw, rfl⟩ := mem_image.mp hc
    obtain ⟨hx,hu⟩ := mem_product.mp hxu
    obtain ⟨hy,hv⟩ := mem_product.mp hyv
    obtain ⟨hz,hw⟩ := mem_product.mp hzw
    change (x+u*t)+(z+w*t)=(y+v*t)+(y+v*t) at heq
    have hi : ((x:ℤ)+u*(t:ℤ))+(z+w*(t:ℤ))=(y+v*(t:ℤ))+(y+v*(t:ℤ)) := by
      exact_mod_cast heq
    have hu' : (u:ℤ) ≤ s := by exact_mod_cast small hu
    have hv' : (v:ℤ) ≤ s := by exact_mod_cast small hv
    have hw' : (w:ℤ) ≤ s := by exact_mod_cast small hw
    have h := strong x hx y hy z hz (2*(v:ℤ)-u-w) (abs_le.mpr (by omega))
      (by linarith [hi] : (x:ℤ)+z-2*y=(2*(v:ℤ)-u-w)*t)
    have hd : u=w := threeAPFree_iff_eq_right.mp freeD hu hv hw (by omega)
    change x+u*t=z+w*t
    rw [h.1,hd]
  have cU : U.card = B.card * rothNumberNat (s+1) := by
    rw [Finset.card_image_of_injOn inj, Finset.card_product, cD]
  rw [← cU]
  apply free.le_rothNumberNat
  · intro a ha
    obtain ⟨⟨x,u⟩,hp,rfl⟩ := mem_image.mp ha
    obtain ⟨hx,hu⟩ := mem_product.mp hp
    exact Nat.add_lt_add_of_lt_of_le (mem_range.mp (hB hx)) (Nat.mul_le_mul_right t (small hu))
  · rfl

/-- Upper occupancy and the total mass control the squared discrepancy of
    the cell averages, including contributions from empty cells. -/
theorem variance_from_cap {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    (μ η : ℝ) (hnon : ∀ i ∈ s, 0 ≤ b i)
    (hcap : ∀ i ∈ s, b i ≤ (1+η)*μ)
    (hmass : ∑ i ∈ s, b i = (s.card : ℝ)*μ) :
    ∑ i ∈ s, (b i - μ)^2 ≤ η*(s.card : ℝ)*μ^2 := by
  have hsq : ∑ i ∈ s, (b i)^2 ≤ ∑ i ∈ s, (1+η)*μ*b i := by
    apply sum_le_sum
    intro i hi
    simpa [pow_two] using mul_le_mul_of_nonneg_right (hcap i hi) (hnon i hi)
  rw [← Finset.mul_sum, hmass] at hsq
  have hpoly : ∀ i, (b i-μ)^2 = (b i)^2 - (2*μ)*b i + μ^2 := by
    intro i
    ring
  simp_rw [hpoly]
  rw [sum_add_distrib, sum_sub_distrib, ← Finset.mul_sum, hmass]
  simp only [sum_const, nsmul_eq_mul]
  linarith only [hsq]

/-- Moving the three points within their cells perturbs the defect by at
    most four cell widths. -/
theorem transport_defect (x y z x' y' z' w : ℤ)
    (hx : |x'-x| ≤ w) (hy : |y'-y| ≤ w) (hz : |z'-z| ≤ w) :
    |(x'+z'-2*y') - (x+z-2*y)| ≤ 4*w := by
  rw [abs_le] at *
  omega

/-- On two sheets with an odd displacement, endpoints have the same tag.
    The projected midpoint defect is then determined exactly by both tags. -/
theorem two_sheet_equation (x y z u i j k : ℤ)
    (hi : i=0 ∨ i=1) (hj : j=0 ∨ j=1) (hk : k=0 ∨ k=1) :
    (2*x+i*(2*u+1))+(2*z+k*(2*u+1)) = 2*(2*y+j*(2*u+1)) ↔
      i=k ∧ x+z-2*y=(j-i)*(2*u+1) := by
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    rcases hk with rfl | rfl <;> simp <;> omega

#print axioms even_thinning_witness
#print axioms expansion_bound
#print axioms variance_from_cap
#print axioms transport_defect
#print axioms two_sheet_equation

end Erdos142Defects
