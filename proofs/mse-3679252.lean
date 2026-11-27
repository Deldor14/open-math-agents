import OMAStatements.S_mse_3679252
import Mathlib

/-! The required open set is the complement of the given closed set. -/
theorem OMA.solution : type_of% @OMA.S_mse_3679252.main := by
  intro X _ F closed sparse
  refine ⟨Fᶜ,closed.isOpen_compl,?_⟩
  rw [frontier_compl,frontier,closed.closure_eq]
  have h : interior F = ∅ := by simpa only [IsNowhereDense,closed.closure_eq] using sparse
  simp [h]
