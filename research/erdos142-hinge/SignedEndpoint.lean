import Mathlib

/-!
# Two real-variable inequalities for moving angular intervals

These are the quantitative steps for upgrading the signed six-width block
of CubeJerry (Left to Solve note 136918) to a bound at its limiting coefficient.
-/

namespace Erdos142SignedEndpoint

/-- A point in the interior with margin η survives motion of both endpoints by at most η. -/
theorem retain_angle {a lo hi lo' hi' η : ℝ}
    (hl : lo + η < a) (hr : a < hi - η)
    (hlo : |lo' - lo| ≤ η) (hhi : |hi' - hi| ≤ η) : lo' < a ∧ a < hi' := by
  obtain ⟨_, h₁⟩ := abs_le.mp hlo
  obtain ⟨h₂, _⟩ := abs_le.mp hhi
  constructor <;> linarith

/-- For ordinary close heights the local angular inequality suffices. For
distant heights or a downward wrap the vertical quadratic pays the entire
angular error while retaining an anisotropic cost in the height coordinate. -/
theorem anisotropic_curvature {sx sy sz ax az ux uy uz C δ : ℝ}
    (hc : 6 ≤ C) (hp : 0 < δ) (hpay : 12 ≤ C*δ^2)
    (hy : 0 ≤ sy) (hang : (ax-az)^2 ≤ 1) (hfold : uy^2 ≤ 1/4)
    (hwrap : sx+sz=2*sy ∨ sx+sz=2*sy+1)
    (hlocal : sx+sz=2*sy → |sx-sz| ≤ δ →
      (ax-az)^2 ≤ 4*(ux^2+uz^2-2*uy^2)) :
    C/4*(sx-sz)^2+(ax-az)^2 ≤
      (C*sx^2+4*ux^2)+(C*sz^2+4*uz^2)-2*(C*sy^2+4*uy^2) := by
  have hc₀ : 0 ≤ C := by linarith
  have hv : 0 ≤ C*(sx-sz)^2 := mul_nonneg hc₀ (sq_nonneg _)
  have hbad : -2 ≤ 4*(ux^2+uz^2-2*uy^2) := by
    nlinarith [sq_nonneg ux, sq_nonneg uz]
  rcases hwrap with hord | hdown
  · have hvid : C*(sx^2+sz^2-2*sy^2) = C/2*(sx-sz)^2 := by
      have he : sy=(sx+sz)/2 := by linarith
      rw [he]
      ring
    by_cases hnear : |sx-sz| ≤ δ
    · nlinarith [hlocal hord hnear]
    · have hlt : δ < |sx-sz| := lt_of_not_ge hnear
      have hsq : δ^2 ≤ (sx-sz)^2 := by
        have h := pow_le_pow_left₀ hp.le hlt.le 2
        simpa using h
      nlinarith [mul_le_mul_of_nonneg_left hsq hc₀]
  · have hvid : C*(sx^2+sz^2-2*sy^2) = C/2*(sx-sz)^2 + 2*C*sy + C/2 := by
      have he : sz=2*sy+1-sx := by linarith
      rw [he]
      ring
    nlinarith [mul_nonneg hc₀ hy]

/-- The extra positive half-turn that can occur in the unshaved moving
intervals has strictly negative folded square curvature. -/
theorem positive_half_turn {x y z : ℝ} (hx : -(1/2) < x) (hx' : x < 0)
    (hz : -(1/2) < z) (hz' : z < 0) (h : x+z-2*y=1/2) :
    x^2+z^2-2*y^2 < 0 := by
  have hd₁ : 0 < 1/2+(x-z) := by linarith
  have hd₂ : 0 < 1/2-(x-z) := by linarith
  have hy : y=(x+z)/2-1/4 := by linarith
  rw [hy]
  nlinarith [mul_pos hd₁ hd₂]

#print axioms positive_half_turn
#print axioms retain_angle
#print axioms anisotropic_curvature

end Erdos142SignedEndpoint
