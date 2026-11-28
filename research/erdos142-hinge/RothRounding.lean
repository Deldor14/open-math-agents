import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic

open Finset

namespace Erdos142Rounding

/-- A strict majority in one integer period contains a pair with any
    prescribed sum, using periodicity to choose the exact representatives. -/
theorem full_sumset (m : ℤ) (hm : 0 < m) (S : ℤ → Prop) [DecidablePred S]
    (periodic : ∀ x j : ℤ, S (x+j*m) ↔ S x)
    (large : (Ico 0 m).card < 2*((Ico 0 m).filter S).card) (t : ℤ) :
    ∃ x z, S x ∧ S z ∧ x+z=t := by
  let A := (Ico 0 m).filter S
  let u := t % m
  have hu : 0 ≤ u ∧ u < m := ⟨Int.emod_nonneg t (by omega), Int.emod_lt_of_pos t hm⟩
  let r := fun x : ℤ => if x ≤ u then u-x else u-x+m
  have rangeR {x : ℤ} (hx : x ∈ Ico 0 m) : r x ∈ Ico 0 m := by
    rw [mem_Ico] at *
    dsimp [r]
    split <;> omega
  have inv {x : ℤ} (hx : x ∈ Ico 0 m) : r (r x) = x := by
    rw [mem_Ico] at hx
    dsimp [r]
    split_ifs <;> omega
  have inRange {x} (hx : x ∈ A) : x ∈ Ico 0 m := (mem_filter.mp hx).1
  have inj : Set.InjOn r (↑A : Set ℤ) := by
    intro x hx y hy eq
    simpa [inv (inRange hx), inv (inRange hy)] using congrArg r eq
  have unionSmall : (A ∪ A.image r).card ≤ (Ico 0 m).card := by
    apply card_le_card
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact inRange hx
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
      exact rangeR (inRange hy)
  have existsPair : ∃ x ∈ A, r x ∈ A := by
    by_contra! hn
    have disj : Disjoint A (A.image r) := by
      rw [Finset.disjoint_left]
      intro x hx hi
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hi
      exact hn y hy hx
    rw [card_union_of_disjoint disj, card_image_of_injOn inj] at unionSmall
    change (Ico 0 m).card < 2*A.card at large
    omega
  obtain ⟨x,hx,hr⟩ := existsPair
  have hs : S (r x) := (mem_filter.mp hr).2
  refine ⟨x,t-x,(mem_filter.mp hx).2,?_,by ring⟩
  have ht : u + (t/m)*m = t := by simpa [u,mul_comm] using Int.emod_add_mul_ediv t m
  dsimp [r] at hs
  split at hs
  · have hh := (periodic (u-x) (t/m)).2 hs
    convert hh using 1
    omega
  · have hh := (periodic (u-x+m) (t/m-1)).2 hs
    convert hh using 1
    linarith

/-- Count the even and odd sites of a doubled period. -/
theorem split_count (m : ℤ) (S : ℤ → Prop) [DecidablePred S] :
    ((Ico 0 (2*m)).filter S).card =
      ((Ico 0 m).filter (fun j => S (2*j))).card +
      ((Ico 0 m).filter (fun j => S (2*j+1))).card := by
  let E := (Ico 0 m).filter (fun j => S (2*j))
  let O := (Ico 0 m).filter (fun j => S (2*j+1))
  have eq : (Ico 0 (2*m)).filter S =
      E.image (fun j => 2*j) ∪ O.image (fun j => 2*j+1) := by
    ext x
    simp only [E,O,mem_union,mem_image,mem_filter,mem_Ico]
    constructor
    · rintro ⟨hx,hs⟩
      by_cases even : x%2=0
      · left
        refine ⟨x/2,⟨by omega,?_⟩,by omega⟩
        rwa [show 2*(x/2)=x by omega]
      · right
        refine ⟨x/2,⟨by omega,?_⟩,by omega⟩
        rwa [show 2*(x/2)+1=x by omega]
    · rintro (⟨j,⟨hj,hs⟩,rfl⟩|⟨j,⟨hj,hs⟩,rfl⟩) <;> exact ⟨by omega,hs⟩
  have disj : Disjoint (E.image (fun j => 2*j)) (O.image (fun j => 2*j+1)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨i,_,hi⟩ := mem_image.mp hx
    obtain ⟨j,_,hj⟩ := mem_image.mp hy
    omega
  rw [eq,card_union_of_disjoint disj,card_image_of_injective _ (by intro a b h; dsimp at h; omega),
    card_image_of_injective _ (by intro a b h; dsimp at h; omega)]

/-- A periodic real midpoint-linear label is constant on any strict majority
    of a cycle of order a power of two. -/
theorem dyadic_rigidity (k : ℕ) (S : ℤ → Prop) [DecidablePred S] (f : ℤ → ℝ)
    (periodic : ∀ x j : ℤ, S (x+j*2^k) ↔ S x)
    (labels : ∀ x j : ℤ, f (x+j*2^k)=f x)
    (mid : ∀ x y z, S x → S y → S z → x+z=2*y → f x+f z=2*f y)
    (large : 2^k < 2*((Ico (0:ℤ) (2^k)).filter S).card) :
    ∃ c, ∀ x, S x → f x=c := by
  induction k generalizing S f with
  | zero =>
    refine ⟨f 0,fun x _ => ?_⟩
    simpa using labels 0 x
  | succ k ih =>
    let m : ℤ := 2^k
    have hm : 0<m := by dsimp [m]; positivity
    have hstep : (2:ℤ)^(k+1)=2*m := by dsimp [m]; ring
    rw [hstep,split_count] at large
    have key (i : ℤ) (h : 2^k < 2*((Ico 0 m).filter (fun j => S (2*j+i))).card) :
        ∃ c, ∀ x, S x → f x=c := by
      let Q := fun j : ℤ => S (2*j+i)
      have per : ∀ x j : ℤ, Q (x+j*m) ↔ Q x := by
        intro x j
        dsimp [Q]
        rw [show 2*(x+j*m)+i=(2*x+i)+j*2^(k+1) by rw [hstep]; ring]
        exact periodic _ _
      have lab : ∀ x j : ℤ, f (2*(x+j*m)+i)=f (2*x+i) := by
        intro x j
        rw [show 2*(x+j*m)+i=(2*x+i)+j*2^(k+1) by rw [hstep]; ring]
        exact labels _ _
      obtain ⟨c,hc⟩ := ih Q (fun j => f (2*j+i)) per lab
        (fun x y z hx hy hz he => mid _ _ _ hx hy hz (by omega)) h
      refine ⟨c,fun y hy => ?_⟩
      have count : (Ico 0 m).card = 2^k := by
        have cast : (2:ℤ)^k = ((2^k : ℕ) : ℤ) := by norm_cast
        rw [Int.card_Ico,sub_zero]
        change ((2:ℤ)^k).toNat=2^k
        rw [cast,Int.toNat_natCast]
      obtain ⟨u,v,hu,hv,he⟩ := full_sumset m hm Q per (by rw [count]; exact h) (y-i)
      have hj := mid _ y _ hu hy hv (by dsimp [Q] at *; omega)
      rw [hc u hu,hc v hv] at hj
      linarith
    have hp : (2:ℕ)^(k+1)=2*2^k := by ring
    rw [hp] at large
    by_cases e : 2^k < 2*((Ico 0 m).filter (fun j => S (2*j))).card
    · exact key 0 (by simpa using e)
    · apply key 1
      omega

/-- The half-phase mask preserves actual three-term-progression freeness.
    This version allows signed shifts and gives the lower construction for
    every rational dilation at most four. -/
theorem half_phase_free (p q b : ℤ) (hp : 0 < p) (hq : 0 < q) (scale : p ≤ 4*q)
    (A : Set ℤ) (free : ThreeAPFree A) :
    ThreeAPFree {y : ℤ | 2*((q*y+b)%p)<p ∧ (q*y+b)/p ∈ A} := by
  intro x hx y hy z hz heq
  obtain ⟨hx,ax⟩ := hx
  obtain ⟨hy,ay⟩ := hy
  obtain ⟨hz,az⟩ := hz
  let u (j : ℤ) := (q*j+b)/p
  let r (j : ℤ) := (q*j+b)%p
  have lower (j : ℤ) : 0 ≤ r j := Int.emod_nonneg _ (by omega)
  have rep (j : ℤ) : r j + p*u j = q*j+b := Int.emod_add_mul_ediv _ _
  change 2*r x < p at hx
  change 2*r y < p at hy
  change 2*r z < p at hz
  have linear : p*(u x+u z-2*u y) = 2*r y-r x-r z := by
    linarith [rep x,rep y,rep z,congrArg (fun j : ℤ => q*j) heq]
  have zero : u x+u z-2*u y=0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have h' : u x+u z-2*u y ≤ -1 := by omega
      have h'' := mul_le_mul_of_nonneg_left h' hp.le
      linarith [lower y]
    · have h' : 1 ≤ u x+u z-2*u y := by omega
      have h'' := mul_le_mul_of_nonneg_left h' hp.le
      linarith [lower x,lower z]
  have same' : u x=u y := free ax ay az (by omega : u x+u z=u y+u y)
  have same : u x=u z := by omega
  have spread : q*(x-z)=r x-r z := by linarith [rep x,rep z,congrArg (fun j : ℤ => p*j) same]
  by_contra hn
  have end_ne : x ≠ z := by omega
  rcases lt_or_gt_of_ne end_ne with h | h
  · have h' : x-z ≤ -2 := by omega
    have h'' := mul_le_mul_of_nonneg_left h' hq.le
    linarith [lower x]
  · have h' : 2 ≤ x-z := by omega
    have h'' := mul_le_mul_of_nonneg_left h' hq.le
    linarith [lower z]

#print axioms full_sumset
#print axioms split_count
#print axioms dyadic_rigidity
#print axioms half_phase_free

/-- With three independent rounding errors, a second difference above four
    error radii remains positive. The label order is retained as well. -/
theorem curved_obstruction (a b c x y z e : ℝ)
    (hx : |x-a| ≤ e) (hy : |y-b| ≤ e) (hz : |z-c| ≤ e)
    (hba : 2*e < b-a) (hcurv : 4*e < a+c-2*b) :
    x < y ∧ y < z ∧ 2*y < x+z := by
  rw [abs_le] at hx hy hz
  exact ⟨by linarith,by linarith,by linarith⟩

/-- Three strictly ordered integer labels with a nonzero midpoint defect
    are themselves a free input that witnesses failure of a rule. -/
theorem free_three_labels (x y z : ℤ) (hxy : x < y) (hyz : y < z)
    (hne : x+z ≠ y+y) : ThreeAPFree ({x,y,z} : Set ℤ) := by
  intro a ha b hb c hc eq
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb hc
  rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl <;>
    rcases hc with rfl|rfl|rfl <;> omega

#print axioms curved_obstruction
#print axioms free_three_labels
end Erdos142Rounding
