import Mathlib

/-! The two-dimensional modular midpoint inequality used in Left to Solve note 136275. -/
noncomputable section
namespace Erdos142Hinge

abbrev Circle := AddCircle (1 : ℝ)

structure Point where
  a : ℝ
  b : ℝ

def s (x : Point) : ℝ := x.a + x.b

def Low (x : Point) : Prop := 1/2 ≤ x.a ∧ s x ≤ 7/6

def High (e : ℝ) (x : Point) : Prop :=
  7/6 + e ≤ s x ∧ ((3/4 ≤ x.a ∧ x.b < 1/2) ∨ (1/4 ≤ x.a ∧ x.a < 1/2 ∧ 1/2 ≤ x.b))

structure Mem (e : ℝ) (x : Point) : Prop where
  a0 : 0 ≤ x.a
  a1 : x.a < 1
  b0 : 0 ≤ x.b
  b1 : x.b < 1
  slo : 2/3 < s x
  shi : s x ≤ 17/12
  part : Low x ∨ High e x

def Mid (x y z : ℝ) : Prop :=
  (x : Circle) + (z : Circle) = (y : Circle) + (y : Circle)

private def Shift (x y z : ℝ) : Prop :=
  2*y = x+z-1 ∨ 2*y = x+z ∨ 2*y = x+z+1

private theorem shift_of_mid {x y z : ℝ} (hx : x ∈ Set.Ico 0 1)
    (hy : y ∈ Set.Ico 0 1) (hz : z ∈ Set.Ico 0 1) (hm : Mid x y z) : Shift x y z := by
  have eq : (((y+y)-(x+z) : ℝ) : Circle) = 0 := by
    rw [AddCircle.coe_sub, AddCircle.coe_add, AddCircle.coe_add]
    exact sub_eq_zero.mpr hm.symm
  obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp eq
  simp only [zsmul_eq_mul, mul_one] at hn
  have lo : (-2:ℝ) < (n:ℝ) := by linarith [hx.2,hy.1,hz.2]
  have hi : (n:ℝ) < 2 := by linarith [hx.1,hy.2,hz.1]
  have li : (-2:ℤ) < n := by exact_mod_cast lo
  have ui : n < (2:ℤ) := by exact_mod_cast hi
  interval_cases n <;> norm_num at hn <;> unfold Shift <;> grind

private theorem high_of_small {e : ℝ} {x : Point} (h : Mem e x) (hs : x.a < 1/2) :
    7/6+e ≤ s x := by
  rcases h.part with low | high
  · linarith [low.1]
  · exact high.1

private theorem low_of_large {e : ℝ} {x : Point} (h : Mem e x)
    (ha : 1/2 ≤ x.a) (hb : 1/2 ≤ x.b) : s x ≤ 7/6 := by
  rcases h.part with low | high
  · exact low.2
  · rcases high.2 with u | v
    · linarith [u.2]
    · linarith [v.2.1]

private theorem slope {e : ℝ} (he : 0 ≤ e) {x y z : Point}
    (hx : Mem e x) (hy : Mem e y) (hz : Mem e z)
    (ha : Shift x.a y.a z.a) (hb : Shift x.b y.b z.b) : 2*s y ≤ s x+s z := by
  by_contra! bad
  have up : s x+s z+1 ≤ 2*s y := by
    rcases ha with h|h|h <;> rcases hb with i|i|i <;> simp only [s] at * <;> linarith
  by_cases small : x.a+z.a < 1
  · by_cases lx : x.a < 1/2
    · linarith [high_of_small hx lx,hz.slo,hy.shi]
    · have lz : z.a < 1/2 := by linarith
      linarith [high_of_small hz lz,hx.slo,hy.shi]
  · have ay : 1/2 ≤ y.a ∧ 1/2 ≤ y.b := by
      rcases ha with h|h|h <;> rcases hb with i|i|i <;>
        simp only [s] at up <;> constructor <;> linarith [hy.a1,hx.b0,hz.b0]
    linarith [low_of_large hy ay.1 ay.2,hx.slo,hz.slo]

private def fold (a : ℝ) := if a < 1/2 then a else a-1/2

private theorem fold_mid {x y z : ℝ} (hx : x ∈ Set.Ico 0 1)
    (hy : y ∈ Set.Ico 0 1) (hz : z ∈ Set.Ico 0 1) (h : Shift x y z) :
    fold y = fold ((x+z)/2) := by
  unfold fold
  split_ifs <;> rcases h with h|h|h <;> linarith [hx.1,hx.2,hy.1,hy.2,hz.1,hz.2]

private theorem fold_upper {a : ℝ} (h : a ∈ Set.Ico 0 1) : (fold a)^2 ≤ 1/4 := by
  unfold fold
  split_ifs with h'
  · nlinarith [mul_nonneg h.1 (show 0 ≤ 1/2-a by linarith),h']
  · nlinarith [mul_nonneg (show 0 ≤ a-1/2 by linarith) (show 0 ≤ 1-a by linarith [h.2]),h.2]

private theorem fold_ge {a : ℝ} (h : 1/4 ≤ a) : (a-1/2)^2 ≤ (fold a)^2 := by
  unfold fold
  split_ifs <;> nlinarith

private theorem chart_gap {a c : ℝ} (ha : 1/4 ≤ a) (hc : 1/4 ≤ c) (m : 1 ≤ a+c) :
    (a-c)^2 ≤ 2*((fold a)^2+(fold c)^2-2*(fold ((a+c)/2))^2) := by
  have hmid : ¬ (a+c)/2 < 1/2 := by linarith
  rw [show fold ((a+c)/2)=(a+c)/2-1/2 by simp only [fold,if_neg hmid]]
  nlinarith [fold_ge ha,fold_ge hc]

private theorem gap_same {e : ℝ} {x z : Point}
    (h : (Low x ∧ Low z) ∨ (High e x ∧ High e z)) :
    (x.a-z.a)^2 ≤ 2*((fold x.a)^2+(fold z.a)^2-2*(fold ((x.a+z.a)/2))^2) := by
  rcases h with ⟨a,b⟩ | ⟨a,b⟩
  · apply chart_gap <;> linarith [a.1,b.1]
  · rcases a.2 with a|a <;> rcases b.2 with b|b
    · apply chart_gap <;> linarith [a.1,b.1]
    · apply chart_gap <;> linarith [a.1,b.1]
    · apply chart_gap <;> linarith [a.1,b.1]
    · have hm : (x.a+z.a)/2 < 1/2 := by linarith [a.2.1,b.2.1]
      simp only [fold,if_pos a.2.1,if_pos b.2.1,if_pos hm]
      nlinarith

def hinge (e t : ℝ) := max 0 (t-7/6-e/2)

def scaledHeight (e : ℝ) (x : Point) : ℝ :=
  2*(s x)^2 + 4*hinge e (s x) + 2*e*(fold x.a)^2

private theorem hinge_gap (e u v w : ℝ) (h : 2*v ≤ u+w) :
    0 ≤ hinge e u+hinge e w-2*hinge e v := by
  unfold hinge
  simp only [max_def]
  split_ifs <;> linarith

private theorem hinge_cross (e u v w : ℝ) (h : 2*v ≤ u+w)
    (sep : (u ≤ 7/6 ∧ 7/6+e ≤ w) ∨ (w ≤ 7/6 ∧ 7/6+e ≤ u)) :
    e/2 ≤ hinge e u+hinge e w-2*hinge e v := by
  unfold hinge
  rcases sep with ⟨l,r⟩|⟨l,r⟩ <;> simp only [max_def] <;> split_ifs <;> linarith

/-- Torus midpoint curvature, in the form obtained by multiplying by epsilon. -/
theorem curvature {e : ℝ} (he : 0 < e) {x y z : Point}
    (hx : Mem e x) (hy : Mem e y) (hz : Mem e z)
    (ha : Mid x.a y.a z.a) (hb : Mid x.b y.b z.b) :
    e*(x.a-z.a)^2 + (s x-s z)^2 ≤
      scaledHeight e x + scaledHeight e z - 2*scaledHeight e y := by
  have sa := shift_of_mid ⟨hx.a0,hx.a1⟩ ⟨hy.a0,hy.a1⟩ ⟨hz.a0,hz.a1⟩ ha
  have sb := shift_of_mid ⟨hx.b0,hx.b1⟩ ⟨hy.b0,hy.b1⟩ ⟨hz.b0,hz.b1⟩ hb
  have mono := slope he.le hx hy hz sa sb
  have sq : (s x-s z)^2 ≤ 2*((s x)^2+(s z)^2-2*(s y)^2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr mono)
      (show 0 ≤ s x+s z+2*s y by linarith [hx.slo,hz.slo,hy.slo])]
  have fmid := fold_mid ⟨hx.a0,hx.a1⟩ ⟨hy.a0,hy.a1⟩ ⟨hz.a0,hz.a1⟩ sa
  unfold scaledHeight
  by_cases same : (Low x ∧ Low z) ∨ (High e x ∧ High e z)
  · have g := gap_same same
    rw [← fmid] at g
    nlinarith [mul_le_mul_of_nonneg_left g he.le,hinge_gap e _ _ _ mono]
  · have sep : (s x ≤ 7/6 ∧ 7/6+e ≤ s z) ∨ (s z ≤ 7/6 ∧ 7/6+e ≤ s x) := by
      rcases hx.part with l|r <;> rcases hz.part with a|b
      · exact (same (Or.inl ⟨l,a⟩)).elim
      · exact Or.inl ⟨l.2,b.1⟩
      · exact Or.inr ⟨a.2,r.1⟩
      · exact (same (Or.inr ⟨r,b⟩)).elim
    have g : -1 ≤ 2*((fold x.a)^2+(fold z.a)^2-2*(fold y.a)^2) := by
      nlinarith [fold_upper ⟨hy.a0,hy.a1⟩,sq_nonneg (fold x.a),sq_nonneg (fold z.a)]
    have lim : (x.a-z.a)^2 ≤ 1 := by
      nlinarith [mul_nonneg (show 0 ≤ 1-(x.a-z.a) by linarith [hx.a1,hz.a0])
        (show 0 ≤ 1+(x.a-z.a) by linarith [hx.a0,hz.a1])]
    nlinarith [mul_le_mul_of_nonneg_left g he.le,mul_le_mul_of_nonneg_left lim he.le,
      hinge_cross e _ _ _ mono sep]

/-- The scaled height is uniformly bounded on every block. -/
theorem height_bounds {e : ℝ} (he : 0 < e) (he' : e ≤ 1/12) {x : Point} (hx : Mem e x) :
    0 ≤ scaledHeight e x ∧ scaledHeight e x ≤ 10 := by
  have h0 : 0 ≤ hinge e (s x) := le_max_left _ _
  have h1 : hinge e (s x) ≤ 1/4 := max_le (by norm_num) (by linarith [hx.shi])
  have hs : (s x)^2 ≤ (17/12 : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.shi)
      (show 0 ≤ 17/12+s x by linarith [hx.slo])]
  unfold scaledHeight
  constructor
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left (fold_upper ⟨hx.a0,hx.a1⟩) he.le]

/-- A single common height slice controls the entire squared endpoint norm. -/
theorem product_slice {m : ℕ} {e w t : ℝ} (he : 0 < e)
    (x y z : Fin m → Point)
    (hx : ∀ i, Mem e (x i)) (hy : ∀ i, Mem e (y i)) (hz : ∀ i, Mem e (z i))
    (ha : ∀ i, Mid (x i).a (y i).a (z i).a)
    (hb : ∀ i, Mid (x i).b (y i).b (z i).b)
    (xmax : (∑ i, scaledHeight e (x i)) < t+w)
    (ymin : t ≤ ∑ i, scaledHeight e (y i))
    (zmax : (∑ i, scaledHeight e (z i)) < t+w) :
    (∑ i, (e*((x i).a-(z i).a)^2+(s (x i)-s (z i))^2)) < 2*w := by
  have total := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => curvature he (hx i) (hy i) (hz i) (ha i) (hb i))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at total ⊢
  linarith

#print axioms curvature
#print axioms height_bounds
#print axioms product_slice
end Erdos142Hinge
