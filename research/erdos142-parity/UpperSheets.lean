import Mathlib

/-! The high two inverse-doubling sheets of a small torus sumset hole.
Coordinates are height in [0,1) and angle in [-1/2,1/2). -/
noncomputable section
namespace Erdos142Sheets
abbrev Pt := ℝ × ℝ

def distSq (x z : Pt) : ℝ := (x.1-z.1)^2+(x.2-z.2)^2
def mid (x y z : Pt) : Prop :=
  ∃ i j : ℤ, x.1+z.1-2*y.1=i ∧ x.2+z.2-2*y.2=j
def sameSum (x z k : Pt) : Prop :=
  ∃ i j : ℤ, x.1+z.1-k.1=i ∧ x.2+z.2-k.2=j
def newPt (k : Pt) (s : ℤ) : Pt := ((1+k.1)/2,(k.2-s)/2)
def height (k : Pt) : ℝ := (1+k.1)/2
def pot (C U : ℝ) (k : Pt) : ℝ :=
  C*(height k-U)^2+2*(k.1^2+k.2^2)
def chart (x : Pt) : Prop := 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ -(1/2:ℝ) ≤ x.2 ∧ x.2 ≤ 1/2
def holeChart (k : Pt) : Prop := 0 ≤ k.1 ∧ k.1 ≤ 1 ∧ 0 < k.2 ∧ k.2 < 1/2
def sheet (s : ℤ) : Prop := s=0 ∨ s=1

private lemma int_small {i : ℤ} (lo : -(1:ℝ) < (i:ℝ)) (hi : (i:ℝ)<1) : i=0 := by
  have l : -1 < i := by exact_mod_cast lo
  have r : i < 1 := by exact_mod_cast hi
  omega

lemma new_chart {k : Pt} (h : holeChart k) {s : ℤ} (hs : sheet s) : chart (newPt k s) := by
  obtain ⟨x,y,v,w⟩ := h
  rcases hs with rfl | rfl <;> dsimp [chart,newPt] <;> norm_num <;> grind

lemma chart_dist {x z : Pt} (hx : chart x) (hz : chart z) : distSq x z ≤ 2 := by
  obtain ⟨a,b,c,d⟩ := hx
  obtain ⟨e,f,g,h⟩ := hz
  have X : |x.1-z.1| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have Y : |x.2-z.2| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have X' := (sq_le_sq).mpr (by simpa using X : |x.1-z.1| ≤ |(1:ℝ)|)
  have Y' := (sq_le_sq).mpr (by simpa using Y : |x.2-z.2| ≤ |(1:ℝ)|)
  dsimp [distSq]; linarith

lemma no_old_mid {x z k : Pt} {s : ℤ} (avoids : ¬ sameSum x z k) :
    ¬ mid x (newPt k s) z := by
  rintro ⟨i,j,a,b⟩
  apply avoids
  refine ⟨i+1,j-s,?_,?_⟩ <;> push_cast <;> dsimp [newPt] at a b <;> linarith

private lemma height_eq {x y z : ℝ} {U V : ℝ} (a : 0 ≤ x) (b : x ≤ 1)
    (ylo : U ≤ y) (yhi : y ≤ V) (zlo : U ≤ z) (zhi : z ≤ V)
    (low : 0 < 2*U-V) (high : 2*V-U < 1) {i : ℤ} (hi : x+z-2*y=i) :
    x+z=2*y := by
  have iz := int_small (i := i) (by linarith) (by linarith)
  rw [iz,Int.cast_zero] at hi; linarith

private lemma quad_bound {k : Pt} (h : holeChart k) : 2*(k.1^2+k.2^2) ≤ 4 := by
  obtain ⟨a,b,c,d⟩ := h
  nlinarith [mul_nonneg a (sub_nonneg.mpr b),mul_nonneg c.le (show 0≤1-k.2 by linarith)]

lemma new_floor {C U e : ℝ} {k : Pt} (c : 0≤C) (ep : 0≤e) (h : U+e ≤ height k) :
    C*e^2 ≤ pot C U k := by
  have sq := (sq_le_sq₀ ep (show 0 ≤ height k-U by linarith)).mpr (by linarith)
  have x := mul_le_mul_of_nonneg_left sq c
  dsimp [pot]; nlinarith only [x,sq_nonneg k.1,sq_nonneg k.2]

/-- An old endpoint of an old/new -> new progression has height at most U.
Selecting the two high sheets forces the other endpoint to pay the height gap. -/
theorem mixed {C U V e M F : ℝ} {x y z : Pt} {sy sz : ℤ}
    (xx : chart x) (old : x.1 ≤ U) (fo : 0≤F) (mp : 0≤M)
    (c : 0≤C) (ep : 0≤e) (budget : 2*M+10 ≤ C*e^2)
    (hy : holeChart y) (hz : holeChart z) (sz' : sheet sz)
    (yl : U+e ≤ height y) (yu : height y ≤ V)
    (zl : U+e ≤ height z) (zu : height z ≤ V)
    (low : 0 < 2*U-V) (high : 2*V-U<1)
    (rel : mid x (newPt y sy) (newPt z sz)) :
    distSq x (newPt z sz) ≤ F+pot C U z-2*pot C U y := by
  obtain ⟨i,j,hi,_⟩ := rel
  have lin := height_eq xx.1 xx.2.1 (by linarith : U≤height y) yu
    (by linarith : U≤height z) zu low high hi
  have ord : 2*(height y-U) ≤ height z-U := by linarith
  have py : 0≤height y-U := by linarith
  have pz : 0≤height z-U := by linarith
  have s1 := (sq_le_sq₀ (show 0≤2*(height y-U) by linarith) pz).mpr ord
  have s2 := (sq_le_sq₀ ep py).mpr (by linarith)
  have cost := mul_le_mul_of_nonneg_left
    (show 2*e^2 ≤ (height z-U)^2-2*(height y-U)^2 by nlinarith only [s1,s2]) c
  have bd := chart_dist xx (new_chart hz sz')
  have q := quad_bound hy
  dsimp [pot]
  nlinarith only [cost,budget,mp,fo,bd,q,sq_nonneg z.1,sq_nonneg z.2]

/-- If the midpoint is old, the cost of a single new endpoint already suffices. -/
theorem old_midpoint {M C U e F G D : ℝ} {z : Pt}
    (c : 0≤C) (ep : 0≤e) (budget : 2*M+2 ≤ C*e^2)
    (bound : F≤M) (non : 0≤G) (diam : D≤2) (zl : U+e ≤ height z) :
    D ≤ G+pot C U z-2*F := by
  linarith only [new_floor c ep zl, budget,bound,non,diam]

/-- When all three points are new, doubled coordinates lift to an ordinary
midpoint and the two endpoint angular sheets coincide. -/
theorem all_new {x y z : Pt} {sx sy sz : ℤ} {C U V : ℝ}
    (c : 0≤C) (hx : holeChart x) (hy : holeChart y) (hz : holeChart z)
    (xs : sheet sx) (zs : sheet sz)
    (yl : U≤height y) (yu : height y≤V) (zl : U≤height z) (zu : height z≤V)
    (low : 0<2*U-V) (high : 2*V-U<1)
    (rel : mid (newPt x sx) (newPt y sy) (newPt z sz)) :
    distSq (newPt x sx) (newPt z sz) ≤ pot C U x+pot C U z-2*pot C U y := by
  obtain ⟨i,j,hi,hj⟩ := rel
  have xc := new_chart hx xs
  have lin := height_eq xc.1 xc.2.1 yl yu zl zu low high hi
  change height x+height z=2*height y at lin
  have vx : x.1+z.1=2*y.1 := by dsimp [height] at lin;linarith
  let a : ℤ := 2*j+sx+sz-2*sy
  have ay : x.2+z.2-2*y.2=(a:ℝ) := by
    dsimp [a];push_cast;dsimp [newPt] at hj;linarith
  have zero := int_small (i := a) (by linarith [hx.2.2.1,hy.2.2.2,hz.2.2.1])
    (by linarith [hx.2.2.2,hy.2.2.1,hz.2.2.2])
  have vy : x.2+z.2=2*y.2 := by rw [zero,Int.cast_zero] at ay;linarith
  have sheets : sx=sz := by dsimp [a] at zero;rcases xs with rfl|rfl <;> rcases zs with rfl|rfl <;> omega
  have curv : 0≤C*((height x-U)^2+(height z-U)^2-2*(height y-U)^2) := by
    apply mul_nonneg c
    have eq : height y=(height x+height z)/2 := by linarith
    rw [eq]; nlinarith [sq_nonneg (height x-height z)]
  rw [sheets]
  dsimp [distSq,newPt,pot]
  dsimp [height] at curv ⊢
  have e₁ : y.1=(x.1+z.1)/2 := by linarith only [vx]
  have e₂ : y.2=(x.2+z.2)/2 := by linarith only [vy]
  rw [e₁] at curv
  rw [e₁,e₂]
  nlinarith only [curv,sq_nonneg (x.1-z.1),sq_nonneg (x.2-z.2)]

end Erdos142Sheets
#print axioms Erdos142Sheets.no_old_mid
#print axioms Erdos142Sheets.mixed
#print axioms Erdos142Sheets.old_midpoint
#print axioms Erdos142Sheets.all_new
