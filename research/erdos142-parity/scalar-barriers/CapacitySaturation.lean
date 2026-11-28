import Mathlib
/-! Every subcollection of a tight subadditive decomposition is tight. -/
namespace Erdos142CapacitySaturation
open Finset

private theorem sum_le_cost {ι : Type*} [DecidableEq ι] (F : ℕ → ℝ)
    (zero : F 0 = 0) (sub : ∀ a b, F (a+b) ≤ F a+F b)
    (w : ι → ℕ) (c : ι → ℝ) (S : Finset ι) (hw : ∀ i ∈ S, F (w i) ≤ c i) :
    F (∑ i ∈ S, w i) ≤ ∑ i ∈ S, c i := by
  induction S using Finset.induction_on with
  | empty => simp [zero]
  | @insert x s h ih =>
    rw [sum_insert h, sum_insert h]
    apply (sub _ _).trans
    exact add_le_add (hw x (mem_insert_self x s))
      (ih (fun j hj => hw j (mem_insert_of_mem hj)))

theorem tight_subcollection {ι : Type*} [DecidableEq ι] (F : ℕ → ℝ)
    (zero : F 0 = 0) (sub : ∀ a b, F (a+b) ≤ F a+F b)
    (w : ι → ℕ) (c : ι → ℝ) (S T : Finset ι) (hT : T ⊆ S)
    (hw : ∀ i ∈ S, F (w i) ≤ c i) (tight : F (∑ i ∈ S, w i) = ∑ i ∈ S, c i) :
    F (∑ i ∈ T, w i) = ∑ i ∈ T, c i := by
  have ht := sum_le_cost F zero sub w c T (fun _ hj => hw _ (hT hj))
  have hr := sum_le_cost F zero sub w c (S \ T) (fun _ hj => hw _ (mem_sdiff.mp hj).1)
  have h := sub (∑ i ∈ S \ T, w i) (∑ i ∈ T, w i)
  rw [Finset.sum_sdiff hT, tight, ← Finset.sum_sdiff (f:=c) hT] at h
  linarith

end Erdos142CapacitySaturation
#print axioms Erdos142CapacitySaturation.tight_subcollection
