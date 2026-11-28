import Mathlib

namespace Erdos142Terminal

private noncomputable def g : ℝ := 39/125-304098/1000000
private noncomputable def e : ℝ := 5/16-39/125
private noncomputable def p (h : ℝ) := 153/208-61/26*h+24/13*h^2
private noncomputable def bound (l h : ℝ) :=
  g*(1-l^2)*h + (1-2*l)*g/2 -(e+(1-2*l)*h/8)*p h

/-- A tangent lower bound on the extra loss when the last quarter is empty. -/
theorem missing_tail {h a l : ℝ} (hh : 0≤h) (hl' : l≤1) :
    h*((1-l^2)*h-(1-2*l)*a) ≤ a*h+(max 0 (h-a))^2 := by
  by_cases he : h≤a
  · rw [max_eq_left (by linarith)]
    have hz : 0≤2*(1-l)*h*(a-h) := by positivity
    nlinarith only [hz,sq_nonneg ((1-l)*h)]
  · rw [max_eq_right (by linarith)]
    nlinarith only [sq_nonneg (a-l*h)]

/-- The tail estimate in the four-fibre inequality when its last fibre is empty. -/
theorem empty_fourth {a b c : ℝ} (hhalf : c≤1/2) (hdouble : 2*a+c≤1) :
    a+b+c ≤ 5/4-(1/2-b)-|a-1/4| := by
  by_cases ha : 1/4≤a
  · rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_nonpos (by linarith)]
    linarith

/-- Upper tangent for the square root in the optimal affine widening estimate. -/
theorem root_tangent (h : ℝ) :
    Real.sqrt (3*((1-h)^2+h^2)) - 1 - h/2 ≤ p h := by
  have hs := Real.sq_sqrt (show 0≤3*((1-h)^2+h^2) by positivity)
  unfold p
  nlinarith only [hs, sq_nonneg (Real.sqrt (3*((1-h)^2+h^2))-13/8)]


private theorem positive_0 (h : ℝ) (ha : 0 ≤ h) (hb : h ≤ (21/400:ℝ)) :
    0 < bound (1/4:ℝ) h := by
  have hlo : 0≤h-0 := sub_nonneg.mpr ha
  have hhi : 0≤(21/400:ℝ)-h := sub_nonneg.mpr hb
  have hid : bound (1/4:ℝ) h - (245721/8320000000:ℝ) =
      (625259/57330:ℝ)*((21/400:ℝ)-h)^3 +
      (549008/28665:ℝ)*(h-0)*((21/400:ℝ)-h)^2 +
      (239686/28665:ℝ)*(h-0)^2*((21/400:ℝ)-h) := by unfold bound e g p; ring
  have hh : 0≤bound (1/4:ℝ) h-(245721/8320000000:ℝ) := by rw [hid]; positivity
  linarith


private theorem positive_1 (h : ℝ) (ha : (21/400:ℝ) ≤ h) (hb : h ≤ (1/2:ℝ)) :
    0 < bound (1/2:ℝ) h := by
  have hlo : 0≤h-(21/400:ℝ) := sub_nonneg.mpr ha
  have hhi : 0≤(1/2:ℝ)-h := sub_nonneg.mpr hb
  have hid : bound (1/2:ℝ) h - (24909/10400000000:ℝ) =
      (182069/11635000:ℝ)*(h-(21/400:ℝ))*((1/2:ℝ)-h) +
      (171329/11635000:ℝ)*(h-(21/400:ℝ))^2 := by unfold bound e g p; ring
  have hh : 0≤bound (1/2:ℝ) h-(24909/10400000000:ℝ) := by rw [hid]; positivity
  linarith


/-- Algebraic obstruction shared by the two quartile tests. -/
private theorem contradict_tangent {a h l : ℝ} (hh : 0<h) (hl' : l≤1/2)
    (hcap : (4+8*a)*g ≤ h*p h)
    (hquart : g*(a*h+(max 0 (h-a))^2) ≤ e*h*p h) :
    bound l h ≤ 0 := by
  have hg : 0≤g := by norm_num [g]
  have ht := mul_le_mul_of_nonneg_left
    (missing_tail (a:=a) hh.le (by linarith : l≤1)) hg
  have ht' : g*((1-l^2)*h-(1-2*l)*a) ≤ e*p h := by
    apply le_of_mul_le_mul_right (a:=h) _ hh
    nlinarith only [ht,hquart]
  have ha := mul_le_mul_of_nonneg_left hcap (show 0 ≤ (1-2*l)/8 by linarith)
  unfold bound
  nlinarith only [ht',ha]

/-- For all real parameters in the geometric reduction, the two necessary
tests for an area of at least 39/125 are incompatible. -/
theorem impossible {a h : ℝ} (hh : 0<h) (hhi : h≤1/2)
    (hcap : (4+8*a)*(39/125-304098/1000000) ≤ h*(153/208-61/26*h+24/13*h^2))
    (hquart : (39/125-304098/1000000)*(a*h+(max 0 (h-a))^2) ≤
      (5/16-39/125)*h*(153/208-61/26*h+24/13*h^2)) : False := by
  change (4+8*a)*g≤h*p h at hcap
  change g*(a*h+(max 0 (h-a))^2)≤e*h*p h at hquart
  by_cases hcut : h≤21/400
  · exact (not_lt_of_ge (contradict_tangent (l:=1/4) hh (by norm_num)
      hcap hquart)) (positive_0 h hh.le hcut)
  · exact (not_lt_of_ge (contradict_tangent (l:=1/2) hh (by norm_num)
      hcap hquart)) (positive_1 h (by linarith) hhi)

end Erdos142Terminal
#print axioms Erdos142Terminal.missing_tail
#print axioms Erdos142Terminal.empty_fourth
#print axioms Erdos142Terminal.root_tangent
#print axioms Erdos142Terminal.impossible
