import ChargedDigits
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Mixed-radix, carry-free sphere construction for the twelve-dimensional
seed in Deldor14's Erdős 142 note #172398. The finite layer cardinality is
left symbolic throughout the geometric argument. -/

namespace Erdos142Packing
open Finset

def modulus : List ℕ → ℕ
  | [] => 1
  | d :: ds => (2*d-1)*modulus ds

/-- The high digit N sits above all the listed mixed-radix coordinates. -/
def encode : List ℕ → List ℕ → ℕ → ℕ
  | d::ds,x::xs,n => x+(2*d-1)*encode ds xs n
  | _,_,n => n

abbrev cost (f : ℕ → ℕ) (xs : List ℕ) := (xs.map f).sum

private theorem encode_bound {ds xs : List ℕ} (fit : List.Forall₂ (· < ·) xs ds)
    {n N : ℕ} (hn : n<N) : encode ds xs n < modulus ds * N := by
  induction fit with
  | nil => simpa [encode,modulus] using hn
  | @cons x d xs ds hx hxs ih =>
    have digit : x < 2*d-1 := by omega
    have next := Nat.mul_le_mul_left (2*d-1) (Nat.succ_le_of_lt ih)
    rw [Nat.mul_succ] at next
    simp only [encode,modulus,Nat.mul_assoc]
    omega

private theorem carry {b x y z i j k : ℕ} (bb : 0 < b)
    (left : x+z < b) (right : y+y < b)
    (eq : (x+b*i)+(z+b*k)=(y+b*j)+(y+b*j)) :
    x+z=y+y ∧ i+k=j+j := by
  have reorder : x+z+b*(i+k)=y+y+b*(j+j) := by
    simp only [Nat.mul_add]
    omega
  have e := congrArg (fun n => n%b) reorder
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt left,Nat.mod_eq_of_lt right] at e
  refine ⟨e,?_⟩
  exact Nat.eq_of_mul_eq_mul_left bb (by omega)

theorem decode {f : ℕ → ℕ}
    (convex : ∀ x < 31, ∀ y < 31, ∀ z < 31, x+z=y+y →
      f y+f y ≤ f x+f z ∧ (f x+f z=f y+f y → x=y))
    {ds xs ys zs : List ℕ} {i j k : ℕ} (small : ∀ d ∈ ds, d ≤ 31)
    (fx : List.Forall₂ (· < ·) xs ds) (fy : List.Forall₂ (· < ·) ys ds)
    (fz : List.Forall₂ (· < ·) zs ds)
    (eq : encode ds xs i+encode ds zs k=encode ds ys j+encode ds ys j) :
    i+k=j+j ∧ cost f ys + cost f ys ≤ cost f xs + cost f zs ∧
      (cost f xs+cost f zs=cost f ys+cost f ys → xs=ys) := by
  induction fx generalizing ys zs with
  | nil =>
    cases fy; cases fz
    exact ⟨eq,le_rfl,fun _=>rfl⟩
  | @cons x d xs ds hx hxs ih =>
    cases fy with
    | @cons y _ ys _ hy hys =>
      cases fz with
      | @cons z _ zs _ hz hzs =>
        have hd := small d (by simp)
        obtain ⟨first,rest⟩ := carry (by omega : 0 < 2*d-1)
          (show x+z < 2*d-1 by omega) (show y+y < 2*d-1 by omega) eq
        obtain ⟨high,tail,rigid⟩ := ih (fun t ht => small t (List.mem_cons_of_mem _ ht)) hys hzs rest
        obtain ⟨low,same⟩ := convex x (by omega) y (by omega) z (by omega) first
        simp only [cost,List.map_cons,List.sum_cons] at tail rigid ⊢
        exact ⟨high,by omega,fun e => by rw [same (by omega),rigid (by omega)]⟩

/-- Product of any one level of a strictly midpoint-convex digit charge
with an optimal Roth set. The low digits may have unequal widths. -/
theorem level_product (f : ℕ → ℕ) (ds : List ℕ) (D : Finset (List ℕ)) (E N : ℕ)
    (convex : ∀ x < 31, ∀ y < 31, ∀ z < 31, x+z=y+y →
      f y+f y ≤ f x+f z ∧ (f x+f z=f y+f y → x=y))
    (small : ∀ d ∈ ds, d ≤ 31)
    (valid : ∀ xs ∈ D, List.Forall₂ (· < ·) xs ds ∧ cost f xs=E) :
    D.card * rothNumberNat N ≤ rothNumberNat (modulus ds*N) := by
  classical
  obtain ⟨H,hin,hcard,hfree⟩ := rothNumberNat_spec N
  let key := fun p : List ℕ × ℕ => encode ds p.1 p.2
  let P := D ×ˢ H
  let Q := P.image key
  have points {p q r : List ℕ × ℕ} (hp : p ∈ P) (hq : q ∈ P) (hr : r ∈ P)
      (eq : key p+key r=key q+key q) : p=q := by
    obtain ⟨ps,ph⟩ := mem_product.mp hp
    obtain ⟨qs,qh⟩ := mem_product.mp hq
    obtain ⟨rs,rh⟩ := mem_product.mp hr
    obtain ⟨pf,pe⟩ := valid p.1 ps
    obtain ⟨qf,qe⟩ := valid q.1 qs
    obtain ⟨rf,re⟩ := valid r.1 rs
    obtain ⟨high,_,rigid⟩ := decode convex small pf qf rf eq
    exact Prod.ext (rigid (by rw [pe,qe,re])) (hfree ph qh rh high)
  have inj : (P:Set (List ℕ × ℕ)).InjOn key := by
    intro p hp q hq eq
    exact points hp hq hp (by rw [eq])
  have free : ThreeAPFree (Q:Set ℕ) := by
    intro x hx y hy z hz eq
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hy
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hz
    exact congrArg key (points hp hq hr eq)
  have bound : Q.card ≤ rothNumberNat (modulus ds*N) := by
    apply free.le_rothNumberNat Q _ rfl
    intro x hx
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
    obtain ⟨ps,ph⟩ := mem_product.mp hp
    exact encode_bound (valid _ ps).1 (mem_range.mp (hin ph))
  change (P.image key).card ≤ _ at bound
  rw [card_image_of_injOn inj,card_product,hcard] at bound
  exact bound

/-- The quadratic charge centred at 29/2 has discrete second difference
equal to the square of the step. Equality forces a zero step. -/
theorem charge_convex {f : ℕ → ℕ}
    (sq : ∀ j < 31, 8*(f j:ℤ)+1=(2*(j:ℤ)-29)^2)
    (x : ℕ) (hx : x<31) (y : ℕ) (hy : y<31) (z : ℕ) (hz : z<31)
    (mid : x+z=y+y) :
    f y+f y ≤ f x+f z ∧ (f x+f z=f y+f y → x=y) := by
  have m : (x:ℤ)+z=(y:ℤ)+y := by exact_mod_cast mid
  have qz := sq z hz
  rw [show (z:ℤ)=2*(y:ℤ)-x by omega] at qz
  have curvature : (f x:ℤ)+f z = (f y:ℤ)+f y + ((x:ℤ)-y)^2 := by
    nlinarith only [sq x hx,sq y hy,qz]
  constructor
  · exact_mod_cast (show (f y:ℤ)+f y ≤ (f x:ℤ)+f z by
      linarith only [curvature,sq_nonneg ((x:ℤ)-y)])
  · intro c
    have h : (f x:ℤ)+f z = (f y:ℤ)+f y := by exact_mod_cast c
    have e : ((x:ℤ)-y)^2=0 := by linarith only [h,curvature]
    have xy := (sq_eq_zero_iff).mp e
    omega

#print axioms level_product
#print axioms charge_convex
end Erdos142Packing

namespace Erdos142Charged

theorem sphere_product (ds : List ℕ) (E N : ℕ) (small : ∀ d ∈ ds, d ≤ 31) :
    (sphere ds E).card * rothNumberNat N ≤ rothNumberNat (Erdos142Packing.modulus ds*N) :=
  Erdos142Packing.level_product charge ds (sphere ds E) E N
    (Erdos142Packing.charge_convex (fun _ h => charge_sq h)) small
    (fun _ h => mem_sphere.mp h)

theorem charged_product (N : ℕ) :
    (sphere widths 459).card * rothNumberNat N ≤ rothNumberNat ((59^3*61^9)*N) := by
  have small : ∀ d ∈ widths, d ≤ 31 := by simp [widths]
  have exact_modulus : Erdos142Packing.modulus widths = 59^3*61^9 := by decide
  rw [← exact_modulus]
  exact sphere_product widths 459 N small

#print axioms charged_product
end Erdos142Charged
