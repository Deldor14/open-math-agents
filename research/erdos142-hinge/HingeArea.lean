import HingeBlock
import Mathlib

/-! Planar Lebesgue measure of the explicit block certified in HingeBlock. -/
noncomputable section
open MeasureTheory Set
namespace Erdos142Hinge

def planarBlock (e : ℝ) : Set (ℝ × ℝ) := {p | Mem e ⟨p.1,p.2⟩}

private structure Panel where
  l : ℝ
  r : ℝ
  loSlope : ℝ
  loIntercept : ℝ
  hiSlope : ℝ
  hiIntercept : ℝ

private def bot (p : Panel) (x : ℝ) := p.loSlope*x+p.loIntercept
private def top (p : Panel) (x : ℝ) := p.hiSlope*x+p.hiIntercept
private def inner (p : Panel) := regionBetween (bot p) (top p) (Ioo p.l p.r)
private def outer (p : Panel) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc p.l p.r ∧ z.2 ∈ Icc (bot p z.1) (top p z.1)}
private def area (p : Panel) : ℝ :=
  (p.hiSlope-p.loSlope)*(p.r^2-p.l^2)/2+(p.hiIntercept-p.loIntercept)*(p.r-p.l)

private theorem inner_meas (p : Panel) : MeasurableSet (inner p) := by
  exact measurableSet_regionBetween (show Measurable (bot p) by unfold bot; fun_prop)
    (show Measurable (top p) by unfold top; fun_prop) measurableSet_Ioo

private theorem outer_meas (p : Panel) : MeasurableSet (outer p) := by
  exact (measurable_fst measurableSet_Icc).inter ((measurableSet_le
    (show Measurable (fun z : ℝ × ℝ => bot p z.1) by unfold bot; fun_prop)
    measurable_snd).inter (measurableSet_le measurable_snd
    (show Measurable (fun z : ℝ × ℝ => top p z.1) by unfold top; fun_prop)))

private theorem outer_inner (p : Panel) : volume (outer p) = volume (inner p) := by
  change (volume.prod volume) _ = (volume.prod volume) _
  rw [Measure.prod_apply (outer_meas p), Measure.prod_apply (inner_meas p)]
  apply lintegral_congr_ae
  filter_upwards [volume.ae_ne p.l, volume.ae_ne p.r] with x hl hr
  by_cases h : x ∈ Ioo p.l p.r
  · have hc : x ∈ Icc p.l p.r := ⟨h.1.le,h.2.le⟩
    have a : Prod.mk x ⁻¹' outer p = Icc (bot p x) (top p x) := by
      ext t; change (_ ∧ _) ↔ _; simp [hc]
    have b : Prod.mk x ⁻¹' inner p = Ioo (bot p x) (top p x) := by
      ext t; change (_ ∧ _) ↔ _; simp [h]
    rw [a,b,Real.volume_Icc,Real.volume_Ioo]
  · have hc : x ∉ Icc p.l p.r := by
      intro hh
      exact h ⟨lt_of_le_of_ne hh.1 (Ne.symm hl),lt_of_le_of_ne hh.2 hr⟩
    have a : Prod.mk x ⁻¹' outer p = ∅ := by
      ext t; change (_ ∧ _) ↔ False; simp [hc]
    have b : Prod.mk x ⁻¹' inner p = ∅ := by
      ext t; change (_ ∧ _) ↔ False; simp [h]
    rw [a,b]

private theorem inner_area (p : Panel) (hl : p.l ≤ p.r)
    (fit : ∀ x ∈ Ioo p.l p.r, bot p x ≤ top p x) :
    volume (inner p) = ENNReal.ofReal (area p) := by
  have b : Continuous (bot p) := by unfold bot; fun_prop
  have t : Continuous (top p) := by unfold top; fun_prop
  change (volume.prod volume) (regionBetween _ _ _) = _
  rw [volume_regionBetween_eq_integral
    (b.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    (t.integrableOn_Icc.mono_set Ioo_subset_Icc_self) measurableSet_Ioo fit,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hl]
  congr 1
  have eq : top p - bot p =
      fun x => (p.hiSlope-p.loSlope)*x + (p.hiIntercept-p.loIntercept) := by
    ext x; simp only [Pi.sub_apply,top,bot]; ring
  rw [eq, intervalIntegral.integral_add
    ((show Continuous (fun x : ℝ => (p.hiSlope-p.loSlope)*x) by fun_prop).intervalIntegrable ..)
    (continuous_const.intervalIntegrable ..), intervalIntegral.integral_const_mul,
    integral_id, intervalIntegral.integral_const]
  simp [area,smul_eq_mul]; ring

private def panels (e : ℝ) : Fin 6 → Panel :=
  ![⟨1/2,2/3,-1,2/3,-1,7/6⟩, ⟨2/3,1,0,0,-1,7/6⟩,
    ⟨3/4,11/12,-1,7/6+e,0,1/2⟩, ⟨11/12,1,-1,7/6+e,-1,17/12⟩,
    ⟨1/4,5/12,-1,7/6+e,0,1⟩, ⟨5/12,1/2,-1,7/6+e,-1,17/12⟩]

private theorem panels_fit {e : ℝ} (he : e ≤ 1/12) (i : Fin 6) :
    ∀ x ∈ Ioo (panels e i).l (panels e i).r, bot (panels e i) x ≤ top (panels e i) x := by
  intro x ⟨l,r⟩
  fin_cases i <;> norm_num [panels,bot,top] at * <;> linarith

private theorem panels_measure {e : ℝ} (he : e ≤ 1/12) (i : Fin 6) :
    volume (inner (panels e i)) = ENNReal.ofReal (area (panels e i)) := by
  apply inner_area _ _ (panels_fit he i)
  fin_cases i <;> norm_num [panels]

private theorem panel_sum {e : ℝ} (he : e ≤ 1/12) :
    (∑ i : Fin 6, ENNReal.ofReal (area (panels e i))) = ENNReal.ofReal (7/24-e/2) := by
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    simp [Fin.sum_univ_succ,panels,area]; ring
  · intro i hi
    fin_cases i <;> norm_num [panels,area] <;> linarith

private theorem inside {e : ℝ} (he : 0 < e) (i : Fin 6) :
    inner (panels e i) ⊆ planarBlock e := by
  rintro ⟨a,b⟩ ⟨⟨al,ar⟩,⟨bl,br⟩⟩
  change Mem e ⟨a,b⟩
  fin_cases i <;> norm_num [panels,bot,top] at al ar bl br <;>
    constructor <;> (try simp only [s]) <;>
    first
    | linarith
    | left; unfold Low; simp only [s]; constructor <;> linarith
    | right; unfold High; simp only [s]; constructor
      · linarith
      · first | left; constructor <;> linarith | right; refine ⟨?_,?_,?_⟩ <;> linarith

private theorem cover (e : ℝ) : planarBlock e ⊆ ⋃ i, outer (panels e i) := by
  rintro ⟨a,b⟩ h
  change Mem e ⟨a,b⟩ at h
  rcases h with ⟨a0,a1,b0,b1,slo,shi,part⟩
  simp only [s] at slo shi
  rcases part with l|r
  · rcases l with ⟨ah,sl⟩
    simp only [s] at sl
    by_cases split : a ≤ 2/3
    · apply mem_iUnion.mpr; refine ⟨0,?_⟩
      change (1/2 ≤ a ∧ a ≤ 2/3) ∧ ((-1)*a+(2/3) ≤ b ∧ b ≤ (-1)*a+(7/6))
      exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩
    · apply mem_iUnion.mpr; refine ⟨1,?_⟩
      change (2/3 ≤ a ∧ a ≤ 1) ∧ ((0)*a+(0) ≤ b ∧ b ≤ (-1)*a+(7/6))
      exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩
  · rcases r with ⟨sl,h|h⟩
    · rcases h with ⟨ah,bh⟩
      simp only [s] at sl
      by_cases split : a ≤ 11/12
      · apply mem_iUnion.mpr; refine ⟨2,?_⟩
        change (3/4 ≤ a ∧ a ≤ 11/12) ∧ ((-1)*a+(7/6+e) ≤ b ∧ b ≤ (0)*a+(1/2))
        exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩
      · apply mem_iUnion.mpr; refine ⟨3,?_⟩
        change (11/12 ≤ a ∧ a ≤ 1) ∧ ((-1)*a+(7/6+e) ≤ b ∧ b ≤ (-1)*a+(17/12))
        exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩
    · rcases h with ⟨ah,al,bh⟩
      simp only [s] at sl
      by_cases split : a ≤ 5/12
      · apply mem_iUnion.mpr; refine ⟨4,?_⟩
        change (1/4 ≤ a ∧ a ≤ 5/12) ∧ ((-1)*a+(7/6+e) ≤ b ∧ b ≤ (0)*a+(1))
        exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩
      · apply mem_iUnion.mpr; refine ⟨5,?_⟩
        change (5/12 ≤ a ∧ a ≤ 1/2) ∧ ((-1)*a+(7/6+e) ≤ b ∧ b ≤ (-1)*a+(17/12))
        exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩

private theorem apart {e : ℝ} (he : 0 ≤ e) :
    Pairwise (fun i j : Fin 6 => Disjoint (inner (panels e i)) (inner (panels e j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro ⟨x,y⟩ ⟨⟨a,b⟩,⟨c,d⟩⟩ ⟨⟨u,v⟩,⟨w,z⟩⟩
  fin_cases i <;> fin_cases j <;> norm_num [panels,bot,top] at * <;> linarith

/-- Two-dimensional Lebesgue measure, including the zero-width end slices. -/
theorem block_area {e : ℝ} (he : 0 < e) (he' : e ≤ 1/12) :
    volume (planarBlock e) = ENNReal.ofReal (7/24 - e/2) := by
  apply le_antisymm
  · calc
      _ ≤ volume (⋃ i, outer (panels e i)) := measure_mono (cover e)
      _ ≤ ∑' i, volume (outer (panels e i)) := measure_iUnion_le _
      _ = _ := by simp only [tsum_fintype,outer_inner,panels_measure he',panel_sum he']
  · calc
      _ = volume (⋃ i, inner (panels e i)) := by
        rw [measure_iUnion (apart he.le) (fun i => inner_meas (panels e i))]
        simp only [tsum_fintype,panels_measure he',panel_sum he']
      _ ≤ _ := measure_mono (iUnion_subset (inside he))

/-- The concrete planar region is Borel. -/
theorem measurable_planarBlock (e : ℝ) : MeasurableSet (planarBlock e) := by
  let P : Set (ℝ × ℝ) := {z | (0 ≤ z.1 ∧ z.1 < 1) ∧ (0 ≤ z.2 ∧ z.2 < 1) ∧
    (2/3 < z.1+z.2 ∧ z.1+z.2 ≤ 17/12) ∧
    ((1/2 ≤ z.1 ∧ z.1+z.2 ≤ 7/6) ∨ (7/6+e ≤ z.1+z.2 ∧
    ((3/4 ≤ z.1 ∧ z.2 < 1/2) ∨ (1/4 ≤ z.1 ∧ z.1 < 1/2 ∧ 1/2 ≤ z.2))))}
  have eq : planarBlock e = P := by
    ext z
    constructor
    · intro h
      exact ⟨⟨h.a0,h.a1⟩,⟨h.b0,h.b1⟩,⟨h.slo,h.shi⟩,h.part⟩
    · rintro ⟨⟨a,b⟩,⟨c,d⟩,⟨f,g⟩,h⟩
      exact ⟨a,b,c,d,f,g,h⟩
  rw [eq]
  have ax (c : ℝ) : MeasurableSet {z : ℝ × ℝ | c ≤ z.1} :=
    measurableSet_le measurable_const measurable_fst
  have az (c : ℝ) : MeasurableSet {z : ℝ × ℝ | z.1 < c} :=
    measurableSet_lt measurable_fst measurable_const
  have bx (c : ℝ) : MeasurableSet {z : ℝ × ℝ | c ≤ z.2} :=
    measurableSet_le measurable_const measurable_snd
  have bz (c : ℝ) : MeasurableSet {z : ℝ × ℝ | z.2 < c} :=
    measurableSet_lt measurable_snd measurable_const
  have sx (c : ℝ) : MeasurableSet {z : ℝ × ℝ | c ≤ z.1+z.2} :=
    measurableSet_le measurable_const (measurable_fst.add measurable_snd)
  have st (c : ℝ) : MeasurableSet {z : ℝ × ℝ | c < z.1+z.2} :=
    measurableSet_lt measurable_const (measurable_fst.add measurable_snd)
  have sz (c : ℝ) : MeasurableSet {z : ℝ × ℝ | z.1+z.2 ≤ c} :=
    measurableSet_le (measurable_fst.add measurable_snd) measurable_const
  exact ((ax 0).inter (az 1)).inter (((bx 0).inter (bz 1)).inter
    (((st (2/3)).inter (sz (17/12))).inter
    (((ax (1/2)).inter (sz (7/6))).union ((sx (7/6+e)).inter
    (((ax (3/4)).inter (bz (1/2))).union
    ((ax (1/4)).inter ((az (1/2)).inter (bx (1/2)))))))))

theorem measurable_scaledHeight (e : ℝ) :
    Measurable (fun z : ℝ × ℝ => scaledHeight e ⟨z.1,z.2⟩) := by
  have mf : Measurable (fun z : ℝ × ℝ => if z.1 < 1/2 then z.1 else z.1-1/2) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_const)
      measurable_fst (measurable_fst.sub measurable_const)
  change Measurable (fun z : ℝ × ℝ => 2*(z.1+z.2)^2 +
    4*max 0 (z.1+z.2-7/6-e/2) + 2*e*(if z.1 < 1/2 then z.1 else z.1-1/2)^2)
  exact (show Measurable (fun z : ℝ × ℝ =>
    2*(z.1+z.2)^2+4*max 0 (z.1+z.2-7/6-e/2)) by fun_prop).add
      (measurable_const.mul (mf.pow_const 2))

#print axioms measurable_scaledHeight
#print axioms measurable_planarBlock
#print axioms block_area
end Erdos142Hinge

