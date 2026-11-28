import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Equality on [a+b,a+2b] forces a plateau at exactly half its height
on [a,b]. Continuity is used only to include the endpoints. -/

namespace Erdos142Rigidity
open Set

variable {F : ℝ → ℝ} {a b : ℝ}

private theorem local_step
    (mono : MonotoneOn F (Ici 0))
    (sub : ∀ x ≥ 0, ∀ y ≥ 0, F (x+y) ≤ F x + F y)
    (glue : ∀ x ≥ 0, ∀ y ≥ 0, F x + F y ≤ F (x+y+max x y))
    (ha : 0 ≤ a) (flat : F (a+b)=F (a+2*b))
    {x y : ℝ} (ax : a ≤ x) (xy : x ≤ y) (yb : y ≤ b)
    (leftRoom : y-x ≤ x-a) (rightRoom : 2*(y-x) ≤ b-x) : F x = F y := by
  let z := a+b-x
  have hx : 0 ≤ x := ha.trans ax
  have hy : 0 ≤ y := hx.trans xy
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have l := sub x hx z hz
  rw [show x+z=a+b by dsimp [z];linarith] at l
  have u := glue y hy z hz
  have fit : y+z+max y z ≤ a+2*b := by
    rcases le_total y z with h|h
    · rw [max_eq_right h]; dsimp [z]; linarith
    · rw [max_eq_left h]; dsimp [z]; linarith
  have hi := mono (show y+z+max y z ∈ Ici 0 from
    add_nonneg (add_nonneg hy hz) (le_trans hy (le_max_left _ _)))
    (show a+2*b ∈ Ici 0 from by change 0 ≤ a+2*b;linarith) fit
  exact le_antisymm (mono hx hy xy) (by linarith)

/-- Every compact subinterval of the interior has a uniform positive
admissible step, so a finite chain connects its endpoints. -/
theorem interior_equal
    (mono : MonotoneOn F (Ici 0))
    (sub : ∀ x ≥ 0, ∀ y ≥ 0, F (x+y) ≤ F x + F y)
    (glue : ∀ x ≥ 0, ∀ y ≥ 0, F x + F y ≤ F (x+y+max x y))
    (ha : 0 ≤ a) (flat : F (a+b)=F (a+2*b))
    {u v : ℝ} (au : a < u) (uv : u ≤ v) (vb : v < b) : F u = F v := by
  let d := min (u-a) ((b-v)/2)
  have dp : 0 < d := lt_min (by linarith) (by linarith)
  have dl : d ≤ u-a := min_le_left _ _
  have dr : d ≤ (b-v)/2 := min_le_right _ _
  let t := fun n : ℕ => min v (u+n*d)
  have lower (n : ℕ) : u ≤ t n := le_min uv (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) dp.le))
  have upper (n : ℕ) : t n ≤ v := min_le_left _ _
  have ordered (n : ℕ) : t n ≤ t (n+1) := by
    apply min_le_min_left
    push_cast
    linarith
  have length (n : ℕ) : t (n+1)-t n ≤ d := by
    change min v (u+(↑(n+1):ℝ)*d) - min v (u+(n:ℝ)*d) ≤ d
    by_cases h : v ≤ u+n*d
    · rw [min_eq_left h]
      linarith [upper (n+1)]
    · rw [min_eq_right (le_of_not_ge h)]
      have li : min v (u+(↑(n+1):ℝ)*d) ≤ u+(↑(n+1):ℝ)*d := min_le_right _ _
      push_cast at *
      linarith
  have constant (n : ℕ) : F u = F (t n) := by
    induction n with
    | zero => simp [t,min_eq_right uv]
    | succ n ih =>
      apply ih.trans
      apply local_step mono sub glue ha flat (au.le.trans (lower n))
        (ordered n) ((upper _).trans vb.le)
      · linarith [length n,lower n]
      · linarith [length n,upper n]
  obtain ⟨N,hN⟩ := exists_nat_ge ((v-u)/d)
  have reached : t N=v := min_eq_left (by
    have h := (div_le_iff₀ dp).mp hN
    linarith)
  rw [← reached]
  exact constant N

theorem plateau_half
    (mono : MonotoneOn F (Ici 0))
    (sub : ∀ x ≥ 0, ∀ y ≥ 0, F (x+y) ≤ F x + F y)
    (glue : ∀ x ≥ 0, ∀ y ≥ 0, F x + F y ≤ F (x+y+max x y))
    (ha : 0 ≤ a) (ab : a ≤ b) (cont : ContinuousOn F (Icc a b))
    (flat : F (a+b)=F (a+2*b)) :
    ∀ x ∈ Icc a b, F x = F (a+b)/2 := by
  have pair : F a + F b = F (a+b) := by
    have lo := sub a ha b (ha.trans ab)
    have hi := glue a ha b (ha.trans ab)
    rw [max_eq_right ab,show a+b+b=a+2*b by linarith,←flat] at hi
    exact le_antisymm hi lo
  rcases ab.eq_or_lt with rfl|ab
  · intro x hx
    have eq := le_antisymm hx.2 hx.1
    rw [eq]
    linarith
  let c := (a+b)/2
  have ac : a<c := by dsimp [c];linarith
  have cb : c<b := by dsimp [c];linarith
  have small : Ioo a b ⊆ {x ∈ Icc a b | F x = F c} := by
    intro x hx
    refine ⟨⟨hx.1.le,hx.2.le⟩,?_⟩
    rcases le_total x c with h|h
    · exact interior_equal mono sub glue ha flat hx.1 h cb
    · exact (interior_equal mono sub glue ha flat ac h hx.2).symm
  have closed : IsClosed {x ∈ Icc a b | F x = F c} :=
    isClosed_Icc.isClosed_eq cont (g := fun _ => F c) continuousOn_const
  have all := closure_minimal small closed
  rw [closure_Ioo ab.ne] at all
  have la := (all (left_mem_Icc.mpr ab.le)).2
  have lb := (all (right_mem_Icc.mpr ab.le)).2
  intro x hx
  have eq := (all hx).2
  linarith

#print axioms interior_equal
#print axioms plateau_half
end Erdos142Rigidity
