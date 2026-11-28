import Mathlib

namespace SixRows

structure Widths where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  f : ℝ
  ha : a ≤ 1/2
  hb : b ≤ 1/2
  hc : c ≤ 1/2
  hd : d ≤ 1/2
  he : e ≤ 1/2
  hf : f ≤ 1/2
  aad : 2*a + d ≤ 1
  ace : a + c + e ≤ 1
  aef : a + e + f ≤ 1
  bbe : 2*b + e ≤ 1
  bdf : b + d + f ≤ 1
  ccf : 2*c + f ≤ 1

def deficit (w : Widths) : ℝ := 2-(w.a+w.b+w.c+w.d+w.e+w.f)

theorem positive_rows (w : Widths) (h : deficit w < 1/80) :
    9/80 < w.a ∧ 9/80 < w.b ∧ 9/80 < w.c ∧
    9/80 < w.d ∧ 9/80 < w.e ∧ 9/80 < w.f := by
  obtain ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,r1,r2,r3,r4,r5,r6⟩ := w
  dsimp [deficit] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem inverse_margins {a b c r : ℝ} (h : a+b+c=1-r)
    (hab : a≤b) (hc : c≤1/2) (ha : 9/80<a) (hr : r<1/80) :
    9*r < a ∧ r < (527/10000)*b := by
  constructor <;> linarith

theorem first_obstruction (w : Widths)
    (h : 2*w.a + 2*w.d ≤ 1+2*deficit w) : 1/28 ≤ deficit w := by
  obtain ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,r1,r2,r3,r4,r5,r6⟩ := w
  dsimp [deficit] at *
  linarith

theorem second_obstruction (w : Widths)
    (h : 4*w.c+w.f ≤ 1+4*deficit w) : 1/32 ≤ deficit w := by
  obtain ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,r1,r2,r3,r4,r5,r6⟩ := w
  dsimp [deficit] at *
  linarith

theorem volume_comparison {x : ℝ} (h : 1/80 ≤ 2-6*x) : x ≤ 53/160 := by
  linarith

#print axioms positive_rows
#print axioms inverse_margins
#print axioms first_obstruction
#print axioms second_obstruction
#print axioms volume_comparison
end SixRows
