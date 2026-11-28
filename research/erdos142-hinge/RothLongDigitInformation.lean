import RothFiniteInformation
import FormalConjecturesForMathlib.Combinatorics.AP.Basic

open Finset
open Erdos142DigitInformation
namespace Erdos142LongDigits

/-- Freedom expressed directly by the starting point and the positive step. -/
def Free (k : ℕ) (s : Finset ℕ) : Prop :=
  ∀ x e, 0<e → (∀ i<k, x+i*e ∈ s) → False

theorem free_iff {k : ℕ} (hk : 2≤k) (s : Finset ℕ) :
    Free k s ↔ Set.IsAPOfLengthFree (↑s : Set ℕ) k := by
  classical
  constructor
  · intro fr t sub prog
    obtain ⟨x,e,card,eq⟩ := prog
    have pos : 0<e := by
      by_contra! he
      have ez : e=0 := by omega
      subst e
      have sing : t={x} := by
        rw [eq]
        ext z
        constructor
        · rintro ⟨i,hi,rfl⟩
          simp
        · intro hz
          obtain rfl : z=x := hz
          exact ⟨0,by exact_mod_cast (by omega : 0<k),by simp⟩
      rw [sing] at card
      have ec : (1:ℕ∞)=k := by simpa using card
      have nk : (1:ℕ)=k := by exact_mod_cast ec
      omega
    exfalso
    apply fr x e pos
    intro i hi
    apply sub
    rw [eq]
    exact ⟨i,by exact_mod_cast hi,by simp⟩
  · intro free x e he terms
    let f (i : ℕ) := x+i*e
    let t := (range k).image f
    have sub : (↑t : Set ℕ) ⊆ ↑s := by
      intro z hz
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
      exact terms i (mem_range.mp hi)
    have inj : Function.Injective f := by
      intro a b eq
      exact Nat.eq_of_mul_eq_mul_right he (Nat.add_left_cancel eq)
    have sz : t.card=k := by simp only [t,card_image_of_injective _ inj,card_range]
    have prog : Set.IsAPOfLength (↑t : Set ℕ) k := by
      refine ⟨x,e,?_,?_⟩
      · simp [sz]
      · ext z
        constructor
        · intro hz
          obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
          exact ⟨i,by exact_mod_cast (mem_range.mp hi),by simp [f]⟩
        · rintro ⟨i,hi,rfl⟩
          have h : i<k := by exact_mod_cast hi
          exact mem_image.mpr ⟨i,mem_range.mpr h,by simp [f]⟩
    have cap := free _ sub prog
    have bad : (1:ℕ∞)<k := by exact_mod_cast (by omega : 1<k)
    exact (not_le_of_gt bad) cap

private theorem bound {k w : ℕ} (hk : 2≤k) (s : Finset ℕ)
    (fit : s ⊆ range w) (fr : Free k s) : s.card≤Set.IsAPOfLengthFree.maxCard k w := by
  classical
  let t := s.image (fun x => x+1)
  have sub : t ⊆ Icc 1 w := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    have := mem_range.mp (fit hy)
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  have free : Free k t := by
    intro x e he terms
    obtain ⟨y,hy,ey⟩ := mem_image.mp (terms 0 (by omega))
    have start : x=y+1 := by simpa using ey.symm
    apply fr y e he
    intro i hi
    obtain ⟨z,hz,ez⟩ := mem_image.mp (terms i hi)
    have eq : z=y+i*e := by omega
    rwa [← eq]
  have size : t.card=s.card := card_image_of_injective _ (fun a b (eq : a+1=b+1) => by omega)
  unfold Set.IsAPOfLengthFree.maxCard
  apply le_csSup
  · refine ⟨(Icc 1 w).card,?_⟩
    rintro a ⟨S,hS,_,rfl⟩
    exact card_le_card hS
  · exact ⟨t,sub,(free_iff hk t).mp free,size⟩

/-- Capacity of a digit conditional on all exterior digits, for the
    exact maximal cardinality appearing in Erdős 142. -/
theorem outside (s : Finset ℕ) {k : ℕ} (hk : 2≤k)
    (fr : Set.IsAPOfLengthFree (↑s : Set ℕ) k) {a w : ℕ}
    (ha : 0<a) (hw : 0<w) (r q : ℕ) :
    count s (fun x => (x%a,x/(a*w))) (r,q) ≤ Set.IsAPOfLengthFree.maxCard k w := by
  classical
  let C := s.filter (fun x => (x%a,x/(a*w))=(r,q))
  let digit (x : ℕ) := (x/a)%w
  have reb {x : ℕ} (hx : x ∈ C) : r+a*digit x+(a*w)*q=x := by
    obtain ⟨hr,hq⟩ := Prod.mk.inj (mem_filter.mp hx).2
    simpa only [digit,hr,hq] using digit_rebuild x a w
  have inj : Set.InjOn digit (↑C : Set ℕ) := by
    intro x hx y hy eq
    rw [← reb hx,← reb hy,eq]
  have free : Free k (C.image digit) := by
    intro z e he terms
    apply ((free_iff hk s).mpr fr) (r+a*z+(a*w)*q) (a*e) (Nat.mul_pos ha he)
    intro i hi
    obtain ⟨x,hx,eq⟩ := mem_image.mp (terms i hi)
    have identity := reb hx
    rw [eq] at identity
    convert (mem_filter.mp hx).1 using 1
    rw [← identity]
    ring
  have cap := bound hk (C.image digit) (by
    intro x hx
    obtain ⟨y,_,rfl⟩ := mem_image.mp hx
    exact mem_range.mpr (Nat.mod_lt _ hw)) free
  rw [card_image_of_injOn inj] at cap
  change (C.card:ℝ)≤_
  exact_mod_cast cap

/-- The finite entropy inequality for arbitrary progression length, with
    the same maximum over [1,w] as the upstream statement. -/
theorem multicut (s : Finset ℕ) {k : ℕ} (hk : 2≤k)
    (fr : Set.IsAPOfLengthFree (↑s : Set ℕ) k) (ws : List ℕ)
    (pos : ∀ w ∈ ws, 0<w) (fit : s ⊆ range ws.prod) :
    s.card*Real.log s.card ≤ cutSum s 1 ws +
      s.card*(ws.map (fun w => Real.log (Set.IsAPOfLengthFree.maxCard k w))).sum := by
  have t := telescope_of_count s _ (fun _ _ ha hw => outside s hk fr ha hw) ws pos 1 (by decide)
  rwa [one_mul,mod_end s fit,add_zero,
    log_constant s (fun x => x%1) 0 (fun x _ => Nat.mod_one x)] at t

#print axioms free_iff
#print axioms outside
#print axioms multicut
end Erdos142LongDigits
