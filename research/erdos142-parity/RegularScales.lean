import BehrendModulus

namespace ProgressionParity
open Set.IsAPOfLengthFree

lemma length_mono {l k : ℕ} (hl : 1<l) (hk : l≤k) (N : ℕ) :
    maxCard l N≤maxCard k N := by
  obtain ⟨A,ha,fa,ca⟩ := attained hl N
  rw [← ca]
  apply bound_witness (by omega : 1<k) A ha
  intro a d hd run
  apply fa a d hd
  exact (run_iff_forall _ _ _ _).mpr fun i hi => (run_iff_forall _ _ _ _).mp run i (by omega)

lemma multiple_upper {k : ℕ} (hk : 1<k) (b N : ℕ) :
    maxCard k (b*N)≤b*maxCard k N := by
  induction b with
  | zero => simp [(initial_values hk).1 0 (by omega)]
  | succ b ih =>
    simpa only [Nat.succ_mul] using
      (interval_subadditive hk (b*N) N).trans (Nat.add_le_add_right ih (maxCard k N))

/-- At the jth transition from b^j to b^(j+1), retain at most a fraction q
of the maximum permitted growth b. -/
noncomputable def slowScales (k b J : ℕ) (q : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range J).filter (fun j =>
    (maxCard k (b^(j+1)) : ℝ) ≤ q*(b : ℝ)*(maxCard k (b^j) : ℝ))

private lemma scale_product {k b : ℕ} (hk : 3≤k) {q : ℝ} (hq : 0<q) (J : ℕ) :
    (maxCard k (b^J) : ℝ) ≤ (b : ℝ)^J * q^(slowScales k b J q).card := by
  classical
  induction J with
  | zero =>
    simp [slowScales,(initial_values (by omega : 1<k)).1 1 (by omega)]
  | succ J ih =>
    have base : (maxCard k (b^(J+1)) : ℝ) ≤ (b : ℝ)*maxCard k (b^J) := by
      have h := multiple_upper (by omega : 1<k) b (b^J)
      rw [pow_succ,Nat.mul_comm (b^J) b]
      exact_mod_cast h
    have nn : J ∉ slowScales k b J q := by simp [slowScales]
    by_cases slow : (maxCard k (b^(J+1)) : ℝ) ≤ q*(b : ℝ)*maxCard k (b^J)
    · have sc : slowScales k b (J+1) q = insert J (slowScales k b J q) := by
        simp [slowScales,Finset.range_add_one,Finset.filter_insert,slow]
      rw [sc, Finset.card_insert_of_notMem nn, pow_succ, pow_succ]
      have h := mul_le_mul_of_nonneg_left ih (by positivity : 0 ≤ q*(b : ℝ))
      exact slow.trans (by convert h using 1; ring)
    · have sc : slowScales k b (J+1) q = slowScales k b J q := by
        simp [slowScales, Finset.range_add_one, Finset.filter_insert,slow]
      rw [sc,pow_succ]
      have h := mul_le_mul_of_nonneg_left ih (by positivity : 0 ≤ (b : ℝ))
      exact base.trans (by convert h using 1; ring)

private theorem slow_scale_log {k b : ℕ} (hk : 3≤k) (hb : 2≤b) (J : ℕ)
    {q : ℝ} (hq : 0<q) :
    ((slowScales k b J q).card : ℝ)*(-Real.log q) ≤ 4*Real.sqrt ((J:ℝ)*Real.log b) := by
  have natBound := (roth_le_upstream (b^J)).trans (length_mono (by decide : 1<3) hk (b^J))
  have realBound : (rothNumberNat (b^J) : ℝ) ≤ (maxCard k (b^J) : ℝ) := by exact_mod_cast natBound
  have be := (Behrend.roth_lower_bound (N := b^J)).trans realBound
  have product := scale_product (b := b) hk hq J
  have both := be.trans product
  rw [Nat.cast_pow,Real.log_pow] at both
  have powpos : 0<(b : ℝ)^J := by positivity
  have ex := (le_of_mul_le_mul_left both powpos)
  have logged := Real.log_le_log (Real.exp_pos _) ex
  rw [Real.log_exp,Real.log_pow] at logged
  linarith only [logged]

theorem slow_scale_count {k b : ℕ} (hk : 3≤k) (hb : 2≤b) (J : ℕ)
    {q : ℝ} (hq : 0<q) (hq' : q<1) :
    ((slowScales k b J q).card : ℝ) ≤ 4*Real.sqrt ((J:ℝ)*Real.log b)/(-Real.log q) :=
  (le_div_iff₀ (neg_pos.mpr (Real.log_neg hq hq'))).mpr (slow_scale_log hk hb J hq)

#print axioms slow_scale_count
end ProgressionParity
