import OMAStatements.S_mo_150061
import Mathlib

/-! Yves Cornulier's disk rotation example (MathOverflow comment 384984),
using the entire group of rotations with the discrete topology. Every point
of positive radius is an orbit accumulation point, while the center is not. -/
namespace Deldor14.DiskOrbits
open Filter Set OMA.S_mo_150061
open scoped Topology
private abbrev Disk := ↥(Metric.closedBall (0:ℂ) 1)
private def center : Disk := ⟨0,by simp⟩
private instance : MulAction Circle Disk where
  smul u z := ⟨(u:ℂ)*z.val,by
    have hz := Metric.mem_closedBall.mp z.property
    rw [Metric.mem_closedBall,dist_zero_right,norm_mul,Circle.norm_coe,one_mul]
    simpa only [dist_zero_right] using hz⟩
  one_smul z := Subtype.ext (by change ((1:Circle):ℂ)*z.val=z.val;simp)
  mul_smul u v z := Subtype.ext (by change ((u*v:Circle):ℂ)*z.val=(u:ℂ)*((v:ℂ)*z.val);simp [mul_assoc])
private lemma coe_rot (u:Circle) (z:Disk) : (u • z).val=(u:ℂ)*z.val := rfl
private noncomputable def t (n:ℕ) : ℝ := 1/((n:ℝ)+1)
private lemma tpos (n:ℕ) : 0<t n := by dsimp [t];positivity
private lemma trange (n:ℕ) : t n ∈ Icc (0:ℝ) 1 := ⟨(tpos n).le,by dsimp [t];apply (div_le_iff₀ (by positivity)).mpr;simp⟩
private lemma tlim : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
private lemma moving (z:Disk) (hz:z.val≠0) : z ∈ AccumulationOfOrbits Circle Disk := by
  let s (n:ℕ) := Circle.exp (t n) • z
  refine ⟨z,s,?_,fun n => ⟨Circle.exp (t n),rfl⟩,?_⟩
  · intro n m eq
    have c := congrArg Subtype.val eq
    change ((Circle.exp (t n):Circle):ℂ)*z.val=((Circle.exp (t m):Circle):ℂ)*z.val at c
    have ce : Circle.exp (t n)=Circle.exp (t m) := Subtype.ext (mul_right_cancel₀ hz c)
    have ang := Circle.exp_injOn_Icc (a:=0) (b:=1) (by linarith [Real.pi_gt_three]) (trange n) (trange m) ce
    dsimp [t] at ang
    have den := (div_eq_div_iff (by positivity) (by positivity)).mp ang
    exact_mod_cast (show (n:ℝ)=m by linarith)
  · apply tendsto_subtype_rng.mpr
    change Tendsto (fun n => Complex.exp ((t n : ℂ)*Complex.I)*z.val) atTop (𝓝 z.val)
    have cont : Continuous (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)*z.val) := by fun_prop
    simpa [Function.comp_def] using (cont.tendsto 0).comp tlim
private lemma fixed : center ∉ AccumulationOfOrbits Circle Disk := by
  rintro ⟨z,s,inj,inorb,lim⟩
  have normeq (n:ℕ) : ‖(s n).val‖=‖z.val‖ := by
    obtain ⟨g,e⟩ := inorb n
    rw [←e,coe_rot,norm_mul,Circle.norm_coe,one_mul]
  have cont : Continuous (fun w : Disk => ‖w.val‖) := continuous_norm.comp continuous_subtype_val
  have l := (cont.tendsto center).comp lim
  simp only [Function.comp_def,normeq,center,norm_zero] at l
  have z0 : z.val=0 := norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds l)
  have zero (n:ℕ) : (s n).val=0 := norm_eq_zero.mp (by rw [normeq,z0,norm_zero])
  have same : s 0=s 1 := Subtype.ext ((zero 0).trans (zero 1).symm)
  exact Nat.zero_ne_one (inj same)
theorem refute : ¬ (type_of% @OMA.S_mo_150061.main) := by
  intro H
  letI : TopologicalSpace Circle := ⊥
  letI : DiscreteTopology Circle := ⟨rfl⟩
  letI : ContinuousSMul Circle Disk := ⟨continuous_prod_of_discrete_left.mpr (by
    intro u
    apply Continuous.subtype_mk
    exact (show Continuous (fun z : Disk => (u:ℂ)*z.val) from continuous_const.mul continuous_subtype_val))⟩
  have closed := H Circle Disk
  let s (n:ℕ) : Disk := ⟨(t n:ℂ),by simpa [Metric.mem_closedBall,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (tpos n)] using (trange n).2⟩
  have lim : Tendsto s atTop (𝓝 center) := by
    apply tendsto_subtype_rng.mpr
    simpa [s,center,Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp tlim
  apply fixed
  apply closed.mem_of_tendsto lim
  exact Filter.Eventually.of_forall (fun n => moving (s n) (by simpa [s] using (tpos n).ne'))
end Deldor14.DiskOrbits
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_150061.main) := Deldor14.DiskOrbits.refute
