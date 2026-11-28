import Mathlib

namespace BealSeptic

theorem seventh_symmetric {K : Type*} [CommRing K] (a b : K) :
    64*(a^7+b^7) = (a+b)*((a+b)^6+21*(a+b)^4*(a-b)^2+
      35*(a+b)^2*(a-b)^4+7*(a-b)^6) := by ring

theorem power_chord (z : ℂ) (hz : ‖z‖ = 1) (j : ℕ) :
    ‖z^j-1‖ ≤ (j:ℝ)*‖z-1‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : z^(j+1)-1 = z*(z^j-1)+(z-1) := by ring
    rw [h]
    calc _ ≤ ‖z*(z^j-1)‖+‖z-1‖ := norm_add_le _ _
         _ ≤ _ := by rw [norm_mul,hz,one_mul,Nat.cast_succ]; linarith

theorem sum_indices (n : ℕ) :
    2*(∑ j ∈ Finset.range n, (j:ℝ)) = (n:ℝ)*((n:ℝ)-1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,Nat.cast_succ]; nlinarith

theorem geometric_arc (z : ℂ) (hz : ‖z‖=1) (p : ℕ)
    (close : ((p:ℝ)-1)*‖z-1‖≤1) :
    (p:ℝ)/2 ≤ ‖∑ j ∈ Finset.range p, z^j‖ := by
  have hsum : ‖(∑ j ∈ Finset.range p, z^j)-(p:ℂ)‖ ≤
      (∑ j ∈ Finset.range p, (j:ℝ))*‖z-1‖ := by
    calc _ = ‖∑ j ∈ Finset.range p, (z^j-1)‖ := by simp [Finset.sum_sub_distrib]
         _ ≤ ∑ j ∈ Finset.range p, ‖z^j-1‖ := norm_sum_le _ _
         _ ≤ ∑ j ∈ Finset.range p, (j:ℝ)*‖z-1‖ :=
           Finset.sum_le_sum fun j _ => power_chord z hz j
         _ = _ := by rw [Finset.sum_mul]
  have bound := mul_le_mul_of_nonneg_left close (show (0:ℝ)≤p by positivity)
  have e := sum_indices p
  have ha : (∑ j ∈ Finset.range p, (j:ℝ))*‖z-1‖ ≤ (p:ℝ)/2 := by
    nlinarith only [bound,congrArg (fun t:ℝ => t*‖z-1‖) e]
  have tri := norm_sub_le (∑ j ∈ Finset.range p, z^j)
    ((∑ j ∈ Finset.range p, z^j)-(p:ℂ))
  rw [sub_sub_cancel] at tri
  simp only [Complex.norm_natCast] at tri
  linarith

end BealSeptic
#print axioms BealSeptic.geometric_arc
#print axioms BealSeptic.seventh_symmetric
