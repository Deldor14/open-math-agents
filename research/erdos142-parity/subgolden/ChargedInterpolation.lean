import CyclicFiberGrid
import FiberInterpolation
import ChargedGeometry

/-! Uniform interpolation of the charged mixed-radix seed of @Deldor14
(note #172398). The use of unequal Roth fibres is due to @pwamsley2015
(notes #181029 and #181117). The rational-grid notation is due to @eilamc14.
Rotating the complete charged alphabet averages the two adjacent fibre sizes. -/

namespace Erdos142Charged
open Erdos142Packing Erdos142CyclicFiber Finset

private theorem low_half {ds xs : List ℕ} (fit : List.Forall₂ (· < ·) xs ds) :
    2*encode ds xs 0 < modulus ds := by
  induction fit with
  | nil => decide
  | @cons x d xs ds hx _ ih =>
    let b := 2*d-1
    have small : 2*x<b := by dsimp [b]; omega
    have next := Nat.mul_le_mul_left b (Nat.succ_le_of_lt ih)
    rw [Nat.mul_succ] at next
    change 2*(x+b*encode ds xs 0) < b*modulus ds
    rw [show 2*(x+b*encode ds xs 0)=2*x+b*(2*encode ds xs 0) by ring]
    omega

/-- The digit words give distinct residues with no cyclic three-term progression. -/
theorem cyclic_sphere {ds : List ℕ} {E L : ℕ} [NeZero L]
    (hL : modulus ds=L) (small : ∀ d ∈ ds, d ≤ 31) :
    ∃ D : Finset (Fin L), D.card = (sphere ds E).card ∧ ThreeAPFree (D : Set (Fin L)) := by
  classical
  let value (xs : List ℕ) := encode ds xs 0
  let digit (xs : List ℕ) : Fin L := Fin.ofNat L (value xs)
  have bound {xs} (hx : xs ∈ sphere ds E) : 2*value xs < L :=
    hL ▸ low_half (mem_sphere.mp hx).1
  have val {xs} (hx : xs ∈ sphere ds E) : (digit xs).val=value xs := by
    change value xs % L=value xs
    exact Nat.mod_eq_of_lt (by have := bound hx; omega)
  have rigid {xs ys zs} (hx : xs ∈ sphere ds E) (hy : ys ∈ sphere ds E) (hz : zs ∈ sphere ds E)
      (eq : value xs+value zs=value ys+value ys) : xs=ys := by
    obtain ⟨xf,xe⟩ := mem_sphere.mp hx
    obtain ⟨yf,ye⟩ := mem_sphere.mp hy
    obtain ⟨zf,ze⟩ := mem_sphere.mp hz
    have h := decode (charge_convex (fun _ h => charge_sq h)) small xf yf zf eq
    exact h.2.2 (by change energy xs+energy zs=energy ys+energy ys; rw [xe,ze,ye])
  refine ⟨(sphere ds E).image digit, card_image_of_injOn ?_, ?_⟩
  · intro xs hx ys hy eq
    have hv := congrArg Fin.val eq
    rw [val hx,val hy] at hv
    exact rigid hx hy hx (by rw [hv])
  · intro X hX Y hY Z hZ eq
    obtain ⟨xs,hx,rfl⟩ := mem_image.mp hX
    obtain ⟨ys,hy,rfl⟩ := mem_image.mp hY
    obtain ⟨zs,hz,rfl⟩ := mem_image.mp hZ
    have hv := congrArg Fin.val eq
    simp only [Fin.val_add,val hx,val hy,val hz] at hv
    have left : value xs+value zs<L := by have := bound hx; have := bound hz; omega
    have right : value ys+value ys<L := by have := bound hy; omega
    rw [Nat.mod_eq_of_lt left,Nat.mod_eq_of_lt right] at hv
    exact congrArg digit (rigid hx hy hz hv)

/-- The full seed inequality holds at every nonnegative grid point, including
zero, with no threshold or rounding term. -/
theorem charged_interpolation (A n j : ℕ) (hA : 0 < A) :
    (2303115151489024:ℤ)*Erdos142ExactInterp.P A n j ≤
      Erdos142ExactInterp.P A n ((59^3*61^9)*j) := by
  let L : ℕ := 59^3*61^9
  have pos : 0<L := by decide
  let _ : NeZero L := ⟨pos.ne'⟩
  obtain ⟨D,hcard,hfree⟩ := cyclic_sphere (ds:=widths) (E:=459) (L:=L)
    (by decide) (by simp [widths])
  rw [sphere_card] at hcard
  have h := interpolate_blocks D.card L pos (averaged D hfree) A (j*n) hA
  rw [hcard] at h
  rw [show ((2303115151489024:ℕ):ℤ)=2303115151489024 by decide] at h
  simpa only [Erdos142ExactInterp.P, Nat.mul_assoc, L] using h

#print axioms cyclic_sphere
#print axioms charged_interpolation
end Erdos142Charged
