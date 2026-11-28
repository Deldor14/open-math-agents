import RothSampleColumns
import Mathlib.LinearAlgebra.Matrix.Rank

open Finset
namespace Erdos142DigitCuts

/-- Every filling of the support by nonzero field elements supplies a sample
    of at most its matrix rank. The entries need not be uniform or positive. -/
theorem sampled_of_rank {F : Type*} [Field F] {A : Finset ℕ} {w h : ℕ}
    (fit : A ⊆ range (w*h)) (B : Matrix (Fin w) (Fin h) F)
    (supp : ∀ i j, B i j≠0 ↔ i.val+w*j.val ∈ A) : Sampled A w B.rank := by
  classical
  obtain ⟨κ,a,inj,span,ind⟩ := exists_linearIndependent' F B.col
  let : Finite κ := Finite.of_injective a inj
  let : Fintype κ := Fintype.ofFinite _
  let V := (univ : Finset κ).image (fun k => (a k).val)
  have size : V.card≤B.rank := by
    have c : Fintype.card κ=B.rank := by
      rw [B.rank_eq_finrank_span_cols,← span,finrank_span_eq_card ind]
    exact card_image_le.trans (by simpa using c.le)
  refine ⟨V,size,?_⟩
  intro u hu v loc
  let i : Fin w := ⟨u,hu⟩
  have limit := mem_range.mp (fit loc)
  have vh : v<h := Nat.lt_of_mul_lt_mul_left (by omega : w*v<w*h)
  let j : Fin h := ⟨v,vh⟩
  have nz : B i j≠0 := (supp i j).2 loc
  by_contra! none
  have generator (k : κ) : (B.col (a k)) i=0 := by
    by_contra val
    exact none (a k).val (mem_image_of_mem _ (mem_univ k)) ((supp i (a k)).1 val)
  have belongs : B.col j ∈ Submodule.span F (Set.range (B.col ∘ a)) := by
    rw [span]
    exact Submodule.subset_span (Set.mem_range_self _)
  have vanishes (x : Fin w → F) (mem : x ∈ Submodule.span F (Set.range (B.col ∘ a))) : x i=0 := by
    induction mem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k,rfl⟩ := hx
      exact generator k
    | zero => rfl
    | add x y _ _ hx hy => simpa [Pi.add_apply] using congrArg₂ (·+·) hx hy
    | smul r x _ hx => simp [Pi.smul_apply,hx]
  exact nz (vanishes (B.col j) belongs)

#print axioms sampled_of_rank
end Erdos142DigitCuts
