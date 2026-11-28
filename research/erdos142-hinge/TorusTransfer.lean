import Mathlib

/-!
# Affine transfer from the unit torus to the finite Roth number

The exceptional set controls ordered endpoint differences of modular progressions
in a measurable slice. Only even index differences can occur in an integer
three-term progression, so the union bound uses exactly floor((N-1)/2) events.
-/

open MeasureTheory Set
open scoped ENNReal Classical

namespace Erdos142Hinge

abbrev UnitTorus (d : ℕ) := Fin d → AddCircle (1 : ℝ)

private theorem circle_probability : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by simp [AddCircle.measure_univ]⟩

private theorem torus_probability (d : ℕ) : IsProbabilityMeasure (volume : Measure (UnitTorus d)) := by
  let _ := circle_probability
  infer_instance

private theorem preserves_multiple (d t : ℕ) (ht : 0 < t) :
    MeasurePreserving (fun b : UnitTorus d => t • b) volume volume := by
  have coord : MeasurePreserving (fun x : AddCircle (1 : ℝ) => t • x) volume volume := by
    simpa using Measure.measurePreserving_zsmul (volume : Measure (AddCircle (1 : ℝ)))
      (show (t : ℤ) ≠ 0 by omega)
  exact volume_preserving_pi (ι := Fin d)
    (α' := fun _ => AddCircle (1 : ℝ)) (β' := fun _ => AddCircle (1 : ℝ))
    (f := fun _ x => t • x) (fun _ => coord)

/-- Choose a direction avoiding all even endpoint gaps available in [0,N). -/
theorem exists_avoiding_direction (d N : ℕ) {E : Set (UnitTorus d)} (hE : MeasurableSet E)
    (hsmall : ((↑((N-1)/2)) : ℝ≥0∞) * volume E < 1) :
    ∃ b : UnitTorus d, ∀ k ∈ Finset.range ((N-1)/2), (2*(k+1)) • b ∉ E := by
  classical
  let _ := torus_probability d
  let K := (N-1)/2
  let bad (k : ℕ) := (fun b : UnitTorus d => (2*(k+1)) • b) ⁻¹' E
  have each (k : ℕ) : volume (bad k) = volume E :=
    (preserves_multiple d _ (by positivity)).measure_preimage hE.nullMeasurableSet
  have hu : volume (⋃ k ∈ Finset.range K, bad k) < 1 := by
    refine lt_of_le_of_lt (measure_biUnion_finset_le (Finset.range K) bad) ?_
    simpa [each, nsmul_eq_mul, K] using hsmall
  by_contra! hall
  have heq : (⋃ k ∈ Finset.range K, bad k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro b
    obtain ⟨k,hk,hb⟩ := hall b
    exact Set.mem_iUnion₂.mpr ⟨k,hk,hb⟩
  rw [heq, measure_univ] at hu
  exact (lt_irrefl _ hu)

private theorem hit_count_le (d N : ℕ) (S E : Set (UnitTorus d)) (b u : UnitTorus d)
    (avoid : ∀ k ∈ Finset.range ((N-1)/2), (2*(k+1)) • b ∉ E)
    (gap : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x+z = y+y → z-x ∈ E) :
    ((Finset.range N).filter (fun n => u+n•b ∈ S)).card ≤ rothNumberNat N := by
  classical
  let A := (Finset.range N).filter (fun n => u+n•b ∈ S)
  have ordered (x y z : ℕ) (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
      (hap : x+z=y+y) (hlt : x<z) : False := by
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    have hz' := (Finset.mem_filter.mp hz).2
    have hN := Finset.mem_range.mp (Finset.mem_filter.mp hz).1
    have hmid : (u+x•b)+(u+z•b)=(u+y•b)+(u+y•b) := by
      calc
        _ = (u+u)+(x+z)•b := by rw [add_nsmul]; abel
        _ = (u+u)+(y+y)•b := by rw [hap]
        _ = _ := by rw [add_nsmul]; abel
    have hdiff := gap _ hx' _ hy' _ hz' hmid
    let k := y-x-1
    have hk : k ∈ Finset.range ((N-1)/2) := by
      apply Finset.mem_range.mpr
      dsimp [k]
      omega
    apply avoid k hk
    have hzn : x+2*(k+1)=z := by dsimp [k]; omega
    have hid : (u+z•b)-(u+x•b)=(2*(k+1))•b := by
      rw [← hzn, add_nsmul]
      abel
    rwa [← hid]
  apply ThreeAPFree.le_rothNumberNat A _ (fun _ h => Finset.mem_range.mp (Finset.mem_filter.mp h).1) rfl
  apply threeAPFree_iff_eq_right.mpr
  intro x hx y hy z hz hap
  rcases lt_trichotomy x z with h | h | h
  · exact (ordered x y z hx hy hz hap h).elim
  · exact h
  · exact (ordered z y x hz hy hx (by omega) h).elim

/-- Quantitative transfer to the actual finite Roth number in mathlib. -/
theorem torus_transfer (d N : ℕ) {S E : Set (UnitTorus d)}
    (hS : MeasurableSet S) (hE : MeasurableSet E)
    (gap : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x+z = y+y → z-x ∈ E)
    (hsmall : ((↑((N-1)/2)) : ℝ≥0∞) * volume E < 1) :
    (N : ℝ≥0∞) * volume S ≤ rothNumberNat N := by
  classical
  let _ := torus_probability d
  obtain ⟨b, avoid⟩ := exists_avoiding_direction d N hE hsmall
  let T (n : ℕ) := (fun u : UnitTorus d => u+n•b) ⁻¹' S
  have pres (n : ℕ) := measurePreserving_add_right (volume : Measure (UnitTorus d)) (n•b)
  have hm (n : ℕ) : MeasurableSet (T n) := (pres n).measurable hS
  have hs (n : ℕ) : volume (T n) = volume S := (pres n).measure_preimage hS.nullMeasurableSet
  let I (n : ℕ) := (T n).indicator (fun _ => (1 : ℝ≥0∞))
  have hi (n : ℕ) : Measurable (I n) := measurable_const.indicator (hm n)
  calc
    (N : ℝ≥0∞)*volume S = ∑ n ∈ Finset.range N, ∫⁻ u, I n u := by
      simp [I, hm, hs, nsmul_eq_mul]
    _ = ∫⁻ u, ∑ n ∈ Finset.range N, I n u := (lintegral_finsetSum _ (fun n _ => hi n)).symm
    _ ≤ ∫⁻ _u : UnitTorus d, (rothNumberNat N : ℝ≥0∞) := by
      apply lintegral_mono
      intro u
      simpa [I, T, Set.indicator, Finset.sum_boole] using
        (Nat.cast_le.mpr (hit_count_le d N S E b u avoid gap) :
          ((((Finset.range N).filter (fun n => u+n•b ∈ S)).card : ℕ) : ℝ≥0∞) ≤ rothNumberNat N)
    _ = _ := by simp

#print axioms exists_avoiding_direction
#print axioms torus_transfer

end Erdos142Hinge
