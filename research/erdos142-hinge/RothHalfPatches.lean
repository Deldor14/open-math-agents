import RothRamseyGlue
import Mathlib.Analysis.Normed.Group.Basic

open Finset Erdos142RamseyGlue
namespace Erdos142HalfPatches

/-- Translation by u changes the real-valued test by at most D everywhere. -/
def PeriodBound {G : Type*} [AddCommGroup G] (F : G → ℝ) (D : ℝ) (u : G) :=
  ∀ x, |F (x+u)-F x| ≤ D

/-- These two inequalities distinguish a point and its double. -/
def Patch {G : Type*} [AddCommGroup G] (F : G → ℝ) (D : ℝ) (x : G) :=
  3*D < F x ∧ F (x+x) < -(3*D)

theorem period_neg {G : Type*} [AddCommGroup G] {F : G → ℝ} {D : ℝ} {u : G}
    (h : PeriodBound F D u) : PeriodBound F D (-u) := by
  intro x
  have e := h (x+-u)
  rw [neg_add_cancel_right,abs_sub_comm] at e
  exact e

theorem period_add {G : Type*} [AddCommGroup G] {F : G → ℝ} {D E : ℝ} {u v : G}
    (hu : PeriodBound F D u) (hv : PeriodBound F E v) : PeriodBound F (D+E) (u+v) := by
  intro x
  simpa [add_assoc,add_comm D E] using
    (abs_sub_le (F (x+u+v)) (F (x+u)) (F x)).trans (add_le_add (hv (x+u)) (hu x))

/-- All four ways a midpoint triple can use both regions are impossible. -/
theorem no_mixed {G : Type*} [AddCommGroup G] (F : G → ℝ) {D : ℝ} (hd : 0≤D)
    (odd : ∀ x, F (-x) = -F x) {p p' b b' : G}
    (hp : Patch F D p) (hp' : Patch F D p') (hb : PeriodBound F D b)
    (hb' : PeriodBound F D b') :
    p+p'≠b+b ∧ p+b≠p'+p' ∧ b+b'≠p+p ∧ b+p≠b'+b' := by
  obtain ⟨hp1,hp2⟩ := hp
  obtain ⟨hp1',hp2'⟩ := hp'
  have zero : F 0=0 := by have e := odd 0; simp only [neg_zero] at e; linarith
  refine ⟨?_,?_,?_,?_⟩
  · intro eq
    have pform : -p+(b+b)=p' := by rw [← eq]; abel
    have bound := (abs_le.mp (period_add hb hb (-p))).2
    rw [pform,odd] at bound
    linarith
  · intro eq
    have bound := (abs_le.mp (hb p)).1
    rw [eq] at bound
    linarith
  · intro eq
    have bound := (abs_le.mp (period_add hb hb' 0)).1
    rw [zero_add,eq,zero,sub_zero] at bound
    linarith
  · intro eq
    have pform : b'+b'+-b=p := by rw [← eq]; abel
    have bound := (abs_le.mp (period_add (period_add hb' hb') (period_neg hb) 0)).2
    rw [zero_add,pform,zero,sub_zero] at bound
    linarith

/-- Reflection about a blocked site bounds the size of every universally protected region. -/
theorem reflection_cap {N b : ℕ} (P : Finset ℕ) (fit : P ⊆ range N) (out : b ∉ P)
    (forbid : ∀ x ∈ P, ∀ y ∈ P, x+y=2*b → x=y) :
    P.card ≤ max b (N-1-b) := by
  let distance (x : ℕ) := (x-b)+(b-x)
  have inj : Set.InjOn distance (↑P : Set ℕ) := by
    intro x hx y hy eq
    change x-b+(b-x)=y-b+(b-y) at eq
    by_contra ne
    have mid : x+y=2*b := by omega
    exact ne (forbid _ hx _ hy mid)
  have sub : P.image distance ⊆ Icc 1 (max b (N-1-b)) := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    have small := mem_range.mp (fit hx)
    have diff : x≠b := fun e => out (e ▸ hx)
    simp only [mem_Icc,distance]
    omega
  have cap := card_le_card sub
  rwa [card_image_of_injOn inj,Nat.card_Icc] at cap

/-- A hit in the centered window gives the uniform asymptotic upper constant 1/2. -/
theorem centered_cap {N L : ℕ} (hL : 0<L) (hN : L≤N) (P B : Finset ℕ)
    (fit : P ⊆ range N) (dis : Disjoint P B) (hit : Hits N L B)
    (block : ∀ b ∈ B, ∀ x ∈ P, ∀ y ∈ P, x+y=2*b → x=y) :
    2*P.card ≤ N+L := by
  let a := (N-L)/2
  obtain ⟨i,hi,hb⟩ := hit a 1 (by decide) (by intro j hj; dsimp [a]; omega)
  have upper := reflection_cap P fit (fun hp => (Finset.disjoint_left.mp dis) hp hb)
    (block _ hb)
  dsimp [a] at upper
  omega

/-- Unconditional upper estimate from the definition of a protected pair. -/
theorem protected_cap {N L : ℕ} (hL : 0<L) (hN : L≤N) (P B : Finset ℕ)
    (fit : P ⊆ range N) (dis : Disjoint P B) (hit : Hits N L B)
    (protect : ∀ T ⊆ P, Erdos142LongDigits.Free 3 T → Erdos142LongDigits.Free 3 (T ∪ B)) :
    2*P.card ≤ N+L := by
  apply centered_cap hL hN P B fit dis hit
  intro b hb x hx y hy eq
  by_contra ne
  let T : Finset ℕ := {x,y}
  have sub : T ⊆ P := by
    intro z hz
    simp only [T,mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl <;> assumption
  have fr : Erdos142LongDigits.Free 3 T := by
    intro a q hq terms
    have z := terms 0 (by decide)
    have o := terms 1 (by decide)
    have t := terms 2 (by decide)
    simp only [T,mem_insert,mem_singleton,Nat.zero_mul,Nat.one_mul,Nat.add_zero] at z o t
    omega
  have blocked := protect T sub fr
  let lo := min x y
  let hi := max x y
  have small : lo < b := by dsimp [lo]; omega
  have ends : lo ∈ T ∧ hi ∈ T := by
    by_cases le : x≤y <;> simp [T,lo,hi,le,le_of_not_ge]
  apply blocked lo (b-lo) (by omega)
  intro j hj
  interval_cases j
  · simpa using mem_union_left B ends.1
  · have e : lo+1*(b-lo)=b := by omega
    rw [e]
    exact mem_union_right T hb
  · have e : lo+2*(b-lo)=hi := by dsimp [lo,hi]; omega
    rw [e]
    exact mem_union_left B ends.2

#print axioms protected_cap
#print axioms no_mixed
#print axioms reflection_cap
#print axioms centered_cap
end Erdos142HalfPatches
