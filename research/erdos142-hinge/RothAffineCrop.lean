import RothHeight
import Mathlib.Data.ZMod.Basic

open Finset
namespace Erdos142AffineVariance

def crop {p : ℕ} (n : ℕ) (a b : ZMod p) (A : Finset ℕ) : Finset ℕ :=
  (range n).filter (fun y => (y : ZMod p) ∈ A.image (fun x : ℕ => a*(x : ZMod p)+b))

private theorem lift_eq {p u v : ℕ} (hu : u<p) (hv : v<p) (h : (u : ZMod p)=(v : ZMod p)) :
    u=v := by
  have e := (ZMod.natCast_eq_natCast_iff' u v p).mp h
  simpa only [Nat.mod_eq_of_lt hu,Nat.mod_eq_of_lt hv] using e

/-- No wrap in the source interval. An invertible affine change modulo p
    followed by restriction to the output interval preserves freeness. -/
theorem crop_free {p : ℕ} [Fact p.Prime] {A : Finset ℕ} {n m : ℕ}
    (source : A ⊆ range n) (nowrap : 2*n≤p+1) (out : m≤p)
    (free : ThreeAPFree (↑A : Set ℕ)) (a b : ZMod p) (ha : a≠0) :
    ThreeAPFree (↑(crop m a b A) : Set ℕ) := by
  apply threeAPFree_iff_eq_right.mpr
  intro X hX Y hY Z hZ eq
  obtain ⟨x,hx,ex⟩ := mem_image.mp (mem_filter.mp hX).2
  obtain ⟨y,hy,ey⟩ := mem_image.mp (mem_filter.mp hY).2
  obtain ⟨z,hz,ez⟩ := mem_image.mp (mem_filter.mp hZ).2
  have ed : (X:ZMod p)+Z=Y+Y := by simpa only [Nat.cast_add] using congrArg (fun k : ℕ => (k:ZMod p)) eq
  rw [← ex,← ey,← ez] at ed
  have e : a*((x:ZMod p)+z)=a*((y:ZMod p)+y) := by linear_combination ed
  have s : ((x+z:ℕ):ZMod p)=((y+y:ℕ):ZMod p) := by
    push_cast
    exact mul_left_cancel₀ ha e
  have xx := mem_range.mp (source hx)
  have yy := mem_range.mp (source hy)
  have zz := mem_range.mp (source hz)
  have same := threeAPFree_iff_eq_right.mp free hx hy hz (lift_eq (by omega) (by omega) s)
  have endeq : (X:ZMod p)=Z := by rw [← ex,← ez,same]
  exact lift_eq (lt_of_lt_of_le (mem_range.mp (mem_filter.mp hX).1) out)
    (lt_of_lt_of_le (mem_range.mp (mem_filter.mp hZ).1) out) endeq

#print axioms crop_free
end Erdos142AffineVariance
