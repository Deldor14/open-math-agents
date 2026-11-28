import DoublingLoss
open Finset Filter Topology Asymptotics ProgressionParity Set.IsAPOfLengthFree
namespace Erdos142Loss

noncomputable def R (k N : ℕ) : ℝ := maxCard k N
noncomputable def doublingGap (k N : ℕ) : ℝ := 2*R k N-R k (2*N)
noncomputable def term (g : ℕ → ℝ) (N t : ℕ) : ℝ := g (2^t*N)/(2:ℝ)^(t+1)

lemma gap_nonneg {k : ℕ} (hk : 1<k) (N : ℕ) : 0 ≤ doublingGap k N := by
  apply sub_nonneg.mpr
  unfold R
  exact_mod_cast multiple_upper hk 2 N

theorem sum_gap (k N T : ℕ) :
    ∑ t ∈ range T, term (doublingGap k) N t = R k N - R k (2^T*N)/(2:ℝ)^T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ,ih]
    unfold term doublingGap
    rw [show (2:ℕ)^(T+1)*N=2*(2^T*N) by rw [pow_succ];ring,pow_succ]
    field_simp
    ring

/-- Reconstruct the extremal function from the cost of joining consecutive
halves. The endpoint density limit supplies the boundary term. -/
theorem gap_hasSum {k N : ℕ} (hk : 1<k)
    (zero : Tendsto (fun t:ℕ => R k (2^t*N)/(2:ℝ)^t) atTop (𝓝 0)) :
    HasSum (term (doublingGap k) N) (R k N) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (f := term (doublingGap k) N)
    (fun t => div_nonneg (gap_nonneg hk _) (by positivity)) _).mpr
  simp only [sum_gap]
  simpa using (tendsto_const_nhds (x := R k N)).sub zero

theorem three_tail_zero (N : ℕ) :
    Tendsto (fun t : ℕ => R 3 (2^t*N)/(2:ℝ)^t) atTop (𝓝 0) := by
  by_cases p : N=0
  · subst N; simp [R,upstream_three_eq_roth]
  have np : 0<N := Nat.pos_of_ne_zero p
  have seq : Tendsto (fun t:ℕ => 2^t*N) atTop atTop := by
    apply tendsto_atTop_mono _ (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1<(2:ℕ)))
    intro t
    simpa using Nat.mul_le_mul_left (2^t) np
  have rat := (isLittleO_iff_tendsto' (f := fun n : ℕ => (rothNumberNat n:ℝ))
    (g := fun n : ℕ => (n:ℝ)) (l := atTop) (by filter_upwards [eventually_ge_atTop 1] with n hn; simp [show n≠0 by omega])).mp rothNumberNat_isLittleO_id
  have h := (rat.comp seq).mul_const (N:ℝ)
  simp only [zero_mul] at h
  apply h.congr
  intro t
  change (rothNumberNat (2^t*N):ℝ)/(↑(2^t*N):ℝ)*N = _
  simp only [R,upstream_three_eq_roth,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  field_simp

/-- A relative envelope for an independent candidate for the loss propagates
to the same relative envelope for r, with no prescribed convergence rate. -/
theorem loss_envelope {k N : ℕ} (hk : 1<k)
    (zero : Tendsto (fun t:ℕ => R k (2^t*N)/(2:ℝ)^t) atTop (𝓝 0))
    (g : ℕ → ℝ) {lo hi : ℝ} (lp : 0 ≤ lo)
    (le : ∀ m ≥ N, lo*doublingGap k m ≤ g m ∧ g m ≤ hi*doublingGap k m) :
    Summable (term g N) ∧ lo*R k N ≤ ∑' t, term g N t ∧
      (∑' t, term g N t) ≤ hi*R k N := by
  have z := gap_hasSum hk zero
  have between (t : ℕ) : lo*term (doublingGap k) N t ≤ term g N t ∧
        term g N t ≤ hi*term (doublingGap k) N t := by
    have ng : N ≤ 2^t*N := by
      calc N = 1*N := (one_mul _).symm
           _ ≤ _ := Nat.mul_le_mul_right N (Nat.one_le_pow _ _ (by decide))
    obtain ⟨a,b⟩ := le _ ng
    unfold term
    rw [← mul_div_assoc,← mul_div_assoc]
    exact ⟨div_le_div_of_nonneg_right a (by positivity),div_le_div_of_nonneg_right b (by positivity)⟩
  have pos : ∀ t, 0 ≤ term g N t := fun t =>
    (mul_nonneg lp (div_nonneg (gap_nonneg hk _) (by positivity))).trans (between t).1
  have zs := (z.mul_left hi).summable
  have sg := Summable.of_nonneg_of_le pos (fun t => (between t).2) zs
  exact ⟨sg,hasSum_le (fun t => (between t).1) (z.mul_left lo) sg.hasSum,
    hasSum_le (fun t => (between t).2) sg.hasSum (z.mul_left hi)⟩

theorem three_gap_hasSum (N : ℕ) : HasSum (term (doublingGap 3) N) (R 3 N) :=
  gap_hasSum (by decide) (three_tail_zero N)

end Erdos142Loss
#print axioms Erdos142Loss.loss_envelope
#print axioms Erdos142Loss.three_gap_hasSum
