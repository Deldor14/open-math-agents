import OMAStatements.S_oeis_a327138
import Mathlib

open OMA.S_oeis_a327138

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a327138.main) := by
  classical
  intro hyp
  have low := Real.pi_gt_three
  have high := Real.pi_lt_d2
  have c₄ : Real.cos 4 < 0 := by
    have pos : 0 < Real.cos (4 - Real.pi) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    simpa using pos
  have c₆ : 0 < Real.cos 6 := by
    rw [← Real.cos_sub_two_pi]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith,by linarith⟩
  have r : rise 2 := by
    constructor
    · decide
    · norm_num
      exact c₄.trans c₆
  have p : 1 ≤ rank 2 := by
    unfold rank
    exact Finset.card_pos.mpr ⟨2,Finset.mem_filter.mpr ⟨by decide,r⟩⟩
  obtain ⟨h₁,h₂⟩ := hyp _ 2 p r rfl
  norm_num at h₁ h₂
  by_cases e : rank 2 = 1
  · rw [e] at h₁
    norm_num at h₁
    linarith
  · have h : 2 ≤ rank 2 := by omega
    have hn : (2:ℝ) ≤ rank 2 := by exact_mod_cast h
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) Real.pi_pos.le]
