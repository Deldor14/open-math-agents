import RothPrimeTransversals
import Mathlib.Logic.Equiv.Prod

open Finset
open Erdos142RowSelection
namespace Erdos142PrimeRows

/-- A full reduced cycle visits one residue class exactly once. -/
theorem reduced_cycle {g t : ℕ} (hg : 0<g) (ht : 0<t) (a q : ℕ)
    (unit : q.Coprime t) (u : ℕ) (hu : u<g*t) (residue : u%g=a%g) :
    ∃! i : Fin t, (a+i.val*(g*q))%(g*t)=u := by
  have low (i : Fin t) : (a+i.val*(g*q))%(g*t)=a%g+g*((a/g+i.val*q)%t) := by
    let v := a/g+i.val*q
    have rep : a+i.val*(g*q)=(a%g+g*(v%t))+(g*t)*(v/t) := by
      calc
        _ = a%g+g*v := by dsimp only [v];rw [Nat.mul_add];nlinarith only [Nat.mod_add_div a g]
        _ = _ := by
          nth_rw 1 [← Nat.mod_add_div v t]
          ring
    have small : a%g+g*(v%t)<g*t := by
      have one := Nat.mul_le_mul_left g (Nat.succ_le_of_lt (Nat.mod_lt v ht))
      rw [Nat.mul_succ] at one
      have := Nat.mod_lt a hg
      omega
    rw [rep,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt small]
  let tgt : Fin t := ⟨u/g,(Nat.div_lt_iff_lt_mul hg).mpr (by simpa only [Nat.mul_comm t g] using hu)⟩
  let f (i : Fin t) : Fin t := ⟨(a/g+i.val*q)%t,Nat.mod_lt _ ht⟩
  have bij : Function.Bijective f := residue_bijective ht (a/g) q unit
  obtain ⟨i,hit⟩ := bij.surjective tgt
  have goal (j : Fin t) : (a+j.val*(g*q))%(g*t)=u ↔ f j=tgt := by
    rw [low]
    have ur := Nat.mod_add_div u g
    rw [residue] at ur
    constructor
    · intro e
      apply Fin.ext
      change (a/g+j.val*q)%t=u/g
      exact Nat.eq_of_mul_eq_mul_left hg (Nat.add_left_cancel (e.trans ur.symm))
    · intro e
      have v := congrArg Fin.val e
      change (a/g+j.val*q)%t=u/g at v
      rw [v,ur]
  exact ⟨i,(goal i).2 hit,fun j hj => bij.injective (((goal j).1 hj).trans hit.symm)⟩

/-- Trials outside a test's active tag set do not affect its binomial count. -/
theorem restricted_count {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
    (E : Finset ι) (C : E → Finset Ω) (m : ℕ) (size : ∀ i, (C i).card=m) (bad : Finset ℕ) :
    (univ.filter (fun σ : ι → Ω => (hits C (fun i : E => σ i.val)).card ∈ bad)).card =
      badCount E.card (Fintype.card Ω) m bad * (Fintype.card Ω)^(Fintype.card ι-E.card) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i : ι => i ∈ E) (fun _ => Ω)
  let B := (univ.filter (fun σ : E → Ω => (hits C σ).card ∈ bad))
  let K : Finset (ι → Ω) := univ.filter (fun σ => (hits C (fun i : E => σ i.val)).card ∈ bad)
  have bind (σ : ι → Ω) : σ ∈ K ↔ (e σ).1 ∈ B := by
    simp [K,B,e,Equiv.piEquivPiSubtypeProd]
  have prod : K.image e = B ×ˢ (univ : Finset ({i : ι // i ∉ E} → Ω)) := by
    ext pair
    constructor
    · intro hp
      obtain ⟨σ,hσ,rfl⟩ := mem_image.mp hp
      exact mem_product.mpr ⟨(bind σ).mp hσ,mem_univ _⟩
    · intro hp
      refine mem_image.mpr ⟨e.symm pair,?_,e.apply_symm_apply _⟩
      apply (bind _).mpr
      simpa only [e.apply_symm_apply] using (mem_product.mp hp).1
  have rest : Fintype.card {i : ι // i ∉ E}=Fintype.card ι-E.card := by
    simp
  have cnt := congrArg Finset.card prod
  rw [card_image_of_injective _ e.injective,card_product,card_univ,Fintype.card_fun,rest] at cnt
  have eq := one_test C m size bad
  change K.card=_
  rw [cnt]
  simpa [B] using congrArg (fun v => v*(Fintype.card Ω)^(Fintype.card ι-E.card)) eq

#print axioms reduced_cycle
#print axioms restricted_count
end Erdos142PrimeRows
