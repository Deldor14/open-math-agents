import OMAStatements.S_oeis_a327136
import Mathlib

open OMA.S_oeis_a327136

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a327136.main) := by
  intro hyp
  obtain ⟨h₁,h₂⟩ := hyp 0
  norm_num at h₁ h₂
  have lo : (1 : ℝ) < term 0 := by linarith [Real.pi_gt_three]
  have hi : (term 0 : ℝ) < 2 := by linarith [Real.pi_lt_d2]
  have l : 1 < term 0 := by exact_mod_cast lo
  have u : term 0 < 2 := by exact_mod_cast hi
  omega
