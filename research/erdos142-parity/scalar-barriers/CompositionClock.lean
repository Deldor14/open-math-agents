import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Fold

/-! The least integer calendar satisfying u(j+h) ≥ u(j)+b(h) for each
positive waiting time h, as used for the calibrated scalar construction.
The clock at i is the maximum total weight of any composition of i. -/

namespace Erdos142CompositionClock
open Finset

def weight (b : ℕ → ℕ) {i : ℕ} (c : Composition i) : ℕ :=
  (c.blocks.map b).sum

noncomputable def u (b : ℕ → ℕ) (i : ℕ) : ℕ :=
  (univ : Finset (Composition i)).sup (weight b)

theorem le_u (b : ℕ → ℕ) {i : ℕ} (c : Composition i) : weight b c ≤ u b i :=
  le_sup (s := univ) (f := weight b) (mem_univ c)

theorem winner (b : ℕ → ℕ) (i : ℕ) :
    ∃ c : Composition i, weight b c = u b i := by
  classical
  obtain ⟨c,_,highest⟩ := (univ : Finset (Composition i)).exists_max_image (weight b)
    ⟨Composition.ones i,mem_univ _⟩
  exact ⟨c,le_antisymm (le_u b c) (Finset.sup_le highest)⟩

/-- Attainment expressed directly as a list of positive integers. -/
theorem attained (b : ℕ → ℕ) (i : ℕ) :
    ∃ L : List ℕ, (∀ h ∈ L, 0 < h) ∧ L.sum=i ∧ (L.map b).sum=u b i := by
  obtain ⟨c,win⟩ := winner b i
  exact ⟨c.blocks,fun _ h => c.blocks_pos h,c.blocks_sum,win⟩

@[simp] theorem zero (b : ℕ → ℕ) : u b 0=0 := by
  obtain ⟨c,hc⟩ := winner b 0
  simpa [weight,(c.blocks_eq_nil).mpr rfl] using hc.symm

theorem superadditive (b : ℕ → ℕ) (i j : ℕ) : u b i+u b j ≤ u b (i+j) := by
  obtain ⟨c,hc⟩ := winner b i
  obtain ⟨d,hd⟩ := winner b j
  rw [← hc,← hd]
  simpa [weight,Composition.append] using le_u b (c.append d)

theorem positive_step (b : ℕ → ℕ) (j h : ℕ) (hp : 0 < h) : u b j+b h ≤ u b (j+h) := by
  have single : b h ≤ u b h := by simpa [weight,Composition.single] using le_u b (Composition.single h hp)
  exact (Nat.add_le_add_left single _).trans (superadditive b j h)

/-- Minimality even allows an arbitrary natural initial value for v. -/
theorem minimal (b v : ℕ → ℕ) (step : ∀ j h, 0 < h → v j+b h ≤ v (j+h))
    (i : ℕ) : u b i ≤ v i := by
  have bound (L : List ℕ) (pos : ∀ h ∈ L, 0 < h) : (L.map b).sum ≤ v L.sum := by
    induction L with
    | nil => simp
    | cons h L ih =>
      have small := ih (fun k hk => pos k (List.mem_cons_of_mem _ hk))
      have extra := step L.sum h (pos h (by simp))
      simp only [List.map_cons,List.sum_cons]
      rw [Nat.add_comm h L.sum,Nat.add_comm (b h)]
      exact (Nat.add_le_add_right small _).trans extra
  obtain ⟨L,pos,total,price⟩ := attained b i
  rw [← price,← total]
  exact bound L pos

theorem least (b : ℕ → ℕ) : IsLeast
    {v : ℕ → ℕ | v 0=0 ∧ ∀ j h, 0 < h → v j+b h ≤ v (j+h)} (u b) :=
  ⟨⟨zero b,positive_step b⟩,fun v hv i => minimal b v hv.2 i⟩

#print axioms attained
#print axioms positive_step
#print axioms superadditive
#print axioms least
end Erdos142CompositionClock
