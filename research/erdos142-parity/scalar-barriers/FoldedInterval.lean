import Mathlib

/-! Geometry of arithmetic progressions after reflection around 1/2.
All coordinates are divided by the interval length. -/
namespace Erdos142Folded
open Set

noncomputable def t (x : ℝ) := |x-1/2|

def SameSide (x y z : ℝ) : Prop :=
  (x ≤ 1/2 ∧ y ≤ 1/2 ∧ z ≤ 1/2) ∨ (1/2 ≤ x ∧ 1/2 ≤ y ∧ 1/2 ≤ z)

private theorem not_opposite {x y z r R : ℝ} (ap : x+z=2*y)
    (lx : x ≤ 1/2) (rz : 1/2 ≤ z) (spread : R < 3*r)
    (hx : t x ∈ Icc r R) (hy : r ≤ t y) (hz : t z ∈ Icc r R) : False := by
  have e : t z-t x=2*(y-1/2) := by
    rw [t,t,abs_of_nonneg (sub_nonneg.mpr rz),abs_of_nonpos (sub_nonpos.mpr lx)]
    linarith
  have h : |t z-t x| ≤ R-r := abs_le.mpr ⟨by linarith [hx.2,hz.1],by linarith [hx.1,hz.2]⟩
  rw [e,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at h
  change 2*t y ≤ R-r at h
  linarith

theorem band {x y z r R : ℝ} (ap : x+z=2*y) (spread : R < 3*r)
    (hx : t x ∈ Icc r R) (hy : t y ∈ Icc r R) (hz : t z ∈ Icc r R) :
    SameSide x y z ∧ t x+t z=2*t y := by
  have side : SameSide x y z := by
    by_cases lx : x ≤ 1/2
    · by_cases lz : z ≤ 1/2
      · exact Or.inl ⟨lx,by linarith,lz⟩
      · exact False.elim (not_opposite ap lx (le_of_not_ge lz) spread hx hy.1 hz)
    · have rx := le_of_not_ge lx
      by_cases rz : 1/2 ≤ z
      · exact Or.inr ⟨rx,by linarith,rz⟩
      · exact False.elim (not_opposite (by linarith : z+x=2*y) (le_of_not_ge rz) rx spread hz hy.1 hx)
  refine ⟨side,?_⟩
  rcases side with ⟨sx,sy,sz⟩|⟨sx,sy,sz⟩
  · simp only [t,abs_of_nonpos (sub_nonpos.mpr sx),abs_of_nonpos (sub_nonpos.mpr sy),
      abs_of_nonpos (sub_nonpos.mpr sz)]
    linarith
  · simp only [t,abs_of_nonneg (sub_nonneg.mpr sx),abs_of_nonneg (sub_nonneg.mpr sy),
      abs_of_nonneg (sub_nonneg.mpr sz)]
    linarith

theorem root_window {x y z root : ℝ} (ap : x+z=2*y) (r : root ∈ Icc (1/8) (3/8))
    (hx : |t x-root| ≤ 4/1000) (hy : |t y-root| ≤ 4/1000) (hz : |t z-root| ≤ 4/1000) :
    SameSide x y z ∧ t x+t z=2*t y ∧ t y ∈ Icc (min (t x) (t z)) (max (t x) (t z)) := by
  have fit {a : ℝ} (ha : |a-root| ≤ 4/1000) : a ∈ Icc (root-4/1000) (root+4/1000) := by
    obtain ⟨l,u⟩ := abs_le.mp ha
    exact ⟨by linarith,by linarith⟩
  obtain ⟨side,fold⟩ := band ap (by linarith [r.1]) (fit hx) (fit hy) (fit hz)
  refine ⟨side,fold,?_⟩
  rcases le_total (t x) (t z) with h|h
  · rw [min_eq_left h,max_eq_right h]; exact ⟨by linarith,by linarith⟩
  · rw [min_eq_right h,max_eq_left h]; exact ⟨by linarith,by linarith⟩

/-- Distinct endpoints on one side stay distinct after reflection, so the
middle vertex has strictly median folded coordinate. -/
theorem strict_median {x y z : ℝ} (distinct : x ≠ z) (side : SameSide x y z)
    (fold : t x+t z=2*t y) : t y ∈ Ioo (min (t x) (t z)) (max (t x) (t z)) := by
  have ne : t x ≠ t z := by
    intro e
    apply distinct
    rcases side with ⟨sx,_,sz⟩|⟨sx,_,sz⟩
    · simp only [t,abs_of_nonpos (sub_nonpos.mpr sx),abs_of_nonpos (sub_nonpos.mpr sz)] at e
      linarith
    · simp only [t,abs_of_nonneg (sub_nonneg.mpr sx),abs_of_nonneg (sub_nonneg.mpr sz)] at e
      linarith
  rcases lt_or_gt_of_ne ne with h|h
  · rw [min_eq_left h.le,max_eq_right h.le]; exact ⟨by linarith,by linarith⟩
  · rw [min_eq_right h.le,max_eq_left h.le]; exact ⟨by linarith,by linarith⟩

noncomputable def center (q j : ℕ) : ℝ := 11/50+(j:ℝ)/q

def Accurate (q j : ℕ) (x estimate : ℝ) : Prop :=
  |t x-estimate| ≤ 1/(36*(q:ℝ)) ∧ |estimate-center q j| ≤ 1/(12*(q:ℝ))

theorem radius {q j : ℕ} {x e : ℝ} (qpos : (0:ℝ)<q) (h : Accurate q j x e) :
    |t x-center q j| ≤ 1/(9*(q:ℝ)) := by
  calc |t x-center q j| ≤ |t x-e|+|e-center q j| := abs_sub_le _ _ _
       _ ≤ _ := add_le_add h.1 h.2
       _ = _ := by field_simp;ring

private theorem in_band {q j : ℕ} {x e : ℝ} (qlo : 2 ≤ q) (jhi : j ≤ q/20)
    (h : Accurate q j x e) : t x ∈ Icc (1/7) (1/3) := by
  have qr : (2:ℝ) ≤ q := by exact_mod_cast qlo
  have qp : (0:ℝ)<q := by linarith
  have H := abs_le.mp (radius qp h)
  have l : (0:ℝ) ≤ (j:ℝ)/q := by positivity
  have ji := (Nat.le_div_iff_mul_le (by decide : 0 < 20)).mp jhi
  have u : (j:ℝ)/q ≤ 1/20 := by
    apply (div_le_iff₀ qp).2
    have hmul : (j:ℝ)*20 ≤ q := by exact_mod_cast ji
    linarith
  have rad : 1/(9*(q:ℝ)) ≤ 1/18 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num : 0<(18:ℝ))).2
    linarith
  unfold center at H
  exact ⟨by linarith [H.1],by linarith [H.2]⟩

private theorem scaled {q j : ℕ} {x e : ℝ} (qp : (0:ℝ)<q) (h : Accurate q j x e) :
    |(q:ℝ)*(t x-11/50)-(j:ℝ)| ≤ 1/9 := by
  have m := mul_le_mul_of_nonneg_left (radius qp h) qp.le
  rw [show (q:ℝ)*|t x-center q j| = |(q:ℝ)*(t x-11/50)-(j:ℝ)| by
    rw [←abs_of_pos qp,←abs_mul,abs_of_pos qp]
    congr 1
    unfold center
    field_simp
    ring,
    show (q:ℝ)*(1/(9*(q:ℝ)))=1/9 by field_simp] at m
  exact m

def Physical (right : Bool) (q j : ℕ) (x : ℝ) : Prop :=
  |x-(if right then 1/2+center q j else 1/2-center q j)| ≤ 1/(9*(q:ℝ))

private theorem physical_left {x : ℝ} {q j : ℕ} (side : x ≤ 1/2)
    (h : |t x-center q j| ≤ 1/(9*(q:ℝ))) : Physical false q j x := by
  unfold t at h
  rw [abs_of_nonpos (sub_nonpos.mpr side)] at h
  change |x-(1/2-center q j)| ≤ _
  rwa [show x-(1/2-center q j) = -(-(x-1/2)-center q j) by ring,abs_neg]

private theorem physical_right {x : ℝ} {q j : ℕ} (side : 1/2 ≤ x)
    (h : |t x-center q j| ≤ 1/(9*(q:ℝ))) : Physical true q j x := by
  unfold t at h
  rw [abs_of_nonneg (sub_nonneg.mpr side)] at h
  change |x-(1/2+center q j)| ≤ _
  rwa [show x-(1/2+center q j) = x-1/2-center q j by ring]

theorem same_cell {q i j k : ℕ} {D : Set ℕ} {x y z ex ey ez : ℝ}
    (qlo : 2 ≤ q) (free : ThreeAPFree D) (digits : ∀ n ∈ D, n ≤ q/20)
    (hi : i ∈ D) (hj : j ∈ D) (hk : k ∈ D) (ap : x+z=2*y)
    (hx : Accurate q i x ex) (hy : Accurate q j y ey) (hz : Accurate q k z ez) :
    i=j ∧ k=j ∧ ∃ right : Bool,
      Physical right q j x ∧ Physical right q j y ∧ Physical right q j z := by
  have qp : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  obtain ⟨side,fold⟩ := band ap (by norm_num : (1/3:ℝ)<3*(1/7))
    (in_band qlo (digits _ hi) hx) (in_band qlo (digits _ hj) hy) (in_band qlo (digits _ hk) hz)
  obtain ⟨lx,ux⟩ := abs_le.mp (scaled qp hx)
  obtain ⟨ly,uy⟩ := abs_le.mp (scaled qp hy)
  obtain ⟨lz,uz⟩ := abs_le.mp (scaled qp hz)
  have f := congrArg (fun w : ℝ => (q:ℝ)*w) fold
  have l : (i:ℝ)+k < (j:ℝ)+j+1 := by linarith
  have u : (j:ℝ)+j < (i:ℝ)+k+1 := by linarith
  have l' : i+k < j+j+1 := by exact_mod_cast l
  have u' : j+j < i+k+1 := by exact_mod_cast u
  have eq : i+k = j+j := by omega
  have first := free hi hj hk eq
  have last : k=j := by omega
  subst i k
  refine ⟨rfl,rfl,?_⟩
  rcases side with ⟨sx,sy,sz⟩|⟨sx,sy,sz⟩
  · exact ⟨false,physical_left sx (radius qp hx),physical_left sy (radius qp hy),
      physical_left sz (radius qp hz)⟩
  · exact ⟨true,physical_right sx (radius qp hx),physical_right sy (radius qp hy),
      physical_right sz (radius qp hz)⟩

#print axioms strict_median
#print axioms root_window
#print axioms same_cell
end Erdos142Folded
