import RothPrimeRows
import RothRowSelection
import Mathlib.Data.Finset.Fin

open Finset
open Erdos142LongDigits Erdos142RowSelection
namespace Erdos142PrimeRows

def progression (p a q : ℕ) := (range p).image (fun i => a+i*q)

/-- One progression-free set simultaneously realizes every specified
    coprime-step progression count outside a forbidden binomial tail. -/
theorem progression_selection {k p w T n : ℕ} (pp : 0<p) (hk : 2≤k)
    (guard : 2*w≤p+1) (span : n≤p*T) (U V : Finset ℕ)
    (lowFit : U ⊆ range w) (highFit : V ⊆ range T) (lowFree : Free k U) (highFree : Free k V)
    (F : Finset (ℕ × ℕ)) (unit : ∀ f ∈ F, f.2.Coprime p)
    (fit : ∀ f ∈ F, progression p f.1 f.2 ⊆ range n) (bad : Finset ℕ)
    (budget : F.card*badCount U.card (2*T) V.card bad < (2*T)^U.card) :
    ∃ A ⊆ range n, Set.IsAPOfLengthFree (↑A : Set ℕ) k ∧
      ∀ f ∈ F, ((progression p f.1 f.2) ∩ A).card ∉ bad := by
  classical
  let perm (f : F) : Fin p ≃ Fin p := Equiv.ofBijective _ (residue_bijective pp f.val.1 f.val.2 (unit _ f.property))
  let lift (u : U) : Fin p := ⟨u.val,by have := mem_range.mp (lowFit u.property);omega⟩
  let site (f : F) (u : U) := f.val.1+((perm f).symm (lift u)).val*f.val.2
  have rem (f : F) (u : U) : site f u % p=u.val :=
    congrArg Fin.val ((perm f).apply_symm_apply (lift u))
  have on (f : F) (u : U) : site f u ∈ progression p f.val.1 f.val.2 :=
    mem_image.mpr ⟨_,mem_range.mpr ((perm f).symm (lift u)).isLt,rfl⟩
  have ins (f : F) (u : U) := mem_range.mp (fit _ f.property (on f u))
  have hlt (f : F) (u : U) : site f u/p<T :=
    (Nat.div_lt_iff_lt_mul pp).mpr (by simpa only [Nat.mul_comm T p] using (ins f u).trans_le span)
  let C (f : F) (u : U) : Finset (Fin (2*T)) :=
    (options T (site f u/p) V).attachFin (fun _ hs => mem_range.mp (options_range V highFit hs))
  have sz (f : F) (u : U) : (C f u).card=V.card := by
    rw [show (C f u).card=(options T (site f u/p) V).card from card_attachFin _ _,options_card (hlt f u)]
  have bd : (univ : Finset F).card*badCount (Fintype.card U) (Fintype.card (Fin (2*T))) V.card bad <
      (Fintype.card (Fin (2*T)))^(Fintype.card U) := by simpa using budget
  obtain ⟨σ,pass⟩ := select (univ : Finset F) C V.card bad (fun f _ => sz f) bd
  let shift (x : ℕ) : ℕ := if h : x ∈ U then (σ ⟨x,h⟩).val else 0
  let A := (range n).filter (fun x => x%p ∈ U ∧ x/p ∈ shifted T (shift (x%p)) V)
  have am (x : ℕ) : x ∈ A ↔ x<n ∧ x%p ∈ U ∧ x/p ∈ shifted T (shift (x%p)) V := by simp [A]
  refine ⟨A,filter_subset _ _,(free_iff hk A).mp (fibered_free hk pp guard A U _
    lowFit lowFree (fun u _ => shifted_free (by omega) T (shift u) V highFree)
    (fun z hz => (am z).mp hz |>.2)),?_⟩
  intro f hf
  let ff : F := ⟨f,hf⟩
  have belongs (u : U) : site ff u ∈ A ↔ σ u ∈ C ff u := by
    rw [am,rem]
    have e : shift u.val=(σ u).val := by simp [shift,u.property]
    rw [e]
    simp only [ins ff u,u.property,true_and,C,mem_attachFin,mem_options (hlt ff u)]
  have unique {x : ℕ} (hx : x ∈ progression p f.1 f.2) (u : U) (r : x%p=u.val) : site ff u=x := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    let ii : Fin p := ⟨i,mem_range.mp hi⟩
    have inv : perm ff ii=lift u := Fin.ext r
    have e := congrArg Fin.val ((perm ff).symm_apply_apply ii)
    rw [inv] at e
    exact congrArg (fun i => f.1+i*f.2) e
  have imageEq : (hits (C ff) σ).image (site ff)=progression p f.1 f.2 ∩ A := by
    ext x
    constructor
    · intro hx
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
      exact mem_inter.mpr ⟨on ff u,(belongs u).mpr (mem_filter.mp hu).2⟩
    · intro hx
      obtain ⟨hp,hA⟩ := mem_inter.mp hx
      let u : U := ⟨x%p,((am x).mp hA).2.1⟩
      have e := unique hp u rfl
      exact mem_image.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,(belongs u).mp (e ▸ hA)⟩,e⟩
  have inj : Function.Injective (site ff) := by
    intro u v e
    apply Subtype.ext
    rw [← rem ff u,e,rem]
  rw [← imageEq,card_image_of_injective _ inj]
  exact pass ff (mem_univ _)

#print axioms progression_selection
end Erdos142PrimeRows
