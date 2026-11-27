import OMAStatements.S_mo_253925
import Mathlib

/-! Formalization for CodeGolf's MathOverflow question 253925, answered by
Fedor Petrov in 2016. Here we take a supporting line of the window maximum
itself and translate its contact window in either direction. -/
namespace Deldor14.ConcaveWindows
open Set OMA.S_mo_253925

private theorem support {F : ℝ → ℝ} (hf : ConcaveOn ℝ univ F) (x : ℝ) :
    ∃ s : ℝ, ∀ y, F y ≤ F x+s*(y-x) := by
  let slopes := (fun z : ℝ => (F z-F x)/(z-x)) '' Ioi x
  have non : slopes.Nonempty := ⟨_,x+1,by change x<x+1;linarith,rfl⟩
  have ub (z : ℝ) (hz : z<x) : (F x-F z)/(x-z) ∈ upperBounds slopes := by
    rintro _ ⟨w,hw,rfl⟩
    exact hf.slope_anti_adjacent (mem_univ z) (mem_univ w) hz hw
  have bdd : BddAbove slopes := ⟨_,ub (x-1) (by linarith)⟩
  refine ⟨sSup slopes,fun y => ?_⟩
  rcases lt_trichotomy y x with h|rfl|h
  · have t := le_div_iff₀ (sub_pos.mpr h) |>.mp (csSup_le non (ub y h))
    linarith
  · simp
  · have t := div_le_iff₀ (sub_pos.mpr h) |>.mp (le_csSup bdd (show (F y-F x)/(y-x)∈slopes from ⟨y,h,rfl⟩))
    linarith

theorem result : type_of% @OMA.S_mo_253925.main := by
  classical
  intro G ε hg he
  have cont : Continuous G := continuousOn_univ.mp (hg.continuousOn isOpen_univ)
  let H := Geps G ε
  have maxAt (x : ℝ) : IsGreatest (G '' Icc (x-ε) (x+ε)) (H x) := by
    have comp : IsCompact (G '' Icc (x-ε) (x+ε)) := isCompact_Icc.image cont
    have ne : (G '' Icc (x-ε) (x+ε)).Nonempty := ⟨_,x,⟨by linarith,by linarith⟩,rfl⟩
    obtain ⟨m,hm⟩ := comp.exists_isGreatest ne
    change IsGreatest _ (sSup _)
    rwa [hm.csSup_eq]
  have conc : ConcaveOn ℝ univ H := by
    refine ⟨convex_univ,?_⟩
    intro x _ y _ a b ha hb e
    obtain ⟨z,hz,ez⟩ := (maxAt x).1
    obtain ⟨w,hw,ew⟩ := (maxAt y).1
    have bound : a*z+b*w ∈ Icc (a*x+b*y-ε) (a*x+b*y+ε) := by
      have ep := congrArg (fun t : ℝ => t*ε) e
      change (a+b)*ε=1*ε at ep
      constructor
      · nlinarith [mul_nonneg ha (sub_nonneg.mpr hz.1),mul_nonneg hb (sub_nonneg.mpr hw.1)]
      · nlinarith [mul_nonneg ha (sub_nonneg.mpr hz.2),mul_nonneg hb (sub_nonneg.mpr hw.2)]
    simp only [smul_eq_mul]
    rw [← ez,← ew]
    apply le_trans (hg.2 (mem_univ z) (mem_univ w) ha hb e)
    exact (maxAt _).2 ⟨_,bound,rfl⟩
  choose s hs using support conc
  refine ⟨s,fun x y => ?_⟩
  by_cases sgn : 0 ≤ s x
  · have h₁ : G y ≤ H (y-ε) := (maxAt _).2 ⟨y,⟨by linarith,by linarith⟩,rfl⟩
    have h₂ := hs x (y-ε)
    change G y ≤ H x+s x*(y-x)-ε*|s x|
    rw [abs_of_nonneg sgn]
    linarith
  · have h₁ : G y ≤ H (y+ε) := (maxAt _).2 ⟨y,⟨by linarith,by linarith⟩,rfl⟩
    have h₂ := hs x (y+ε)
    change G y ≤ H x+s x*(y-x)-ε*|s x|
    rw [abs_of_neg (lt_of_not_ge sgn)]
    linarith
end Deldor14.ConcaveWindows
theorem OMA.solution : type_of% @OMA.S_mo_253925.main := Deldor14.ConcaveWindows.result
