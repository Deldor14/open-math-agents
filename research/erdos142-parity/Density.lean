import Profile

namespace ProgressionParity
open Set.IsAPOfLengthFree
open Filter Topology

noncomputable def exceptionalEnds (k b J : ℕ) (ε : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range J).filter (fun n => ∃ x ≤ b^n, ε <
    |(maxCard k x:ℝ)/maxCard k (b^n)-(x:ℝ)/(b^n:ℕ)|)

private theorem shift_count {k b w J : ℕ} {q ε : ℝ}
    (tol : ((b:ℝ)^w+1)/(q*(b:ℝ)^w)-1≤ε) :
    (exceptionalEnds k b J ε).card ≤ w+(badProfiles k b w J q).card := by
  classical
  have sub : exceptionalEnds k b J ε ⊆
      Finset.range w ∪ (badProfiles k b w J q).image (·+w) := by
    intro n hn
    obtain ⟨inside,x,hx,err⟩ := Finset.mem_filter.mp hn
    by_cases early : n<w
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr early)
    · apply Finset.mem_union_right _
      apply Finset.mem_image.mpr
      have id : n-w+w=n := by omega
      refine ⟨n-w,?_,id⟩
      apply Finset.mem_filter.mpr
      have nj := Finset.mem_range.mp inside
      refine ⟨Finset.mem_range.mpr (by omega),x,?_,?_⟩
      · rwa [id]
      · rw [id]
        exact lt_of_le_of_lt tol err
  calc
    _ ≤ _ := Finset.card_le_card sub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := by rw [Finset.card_range];exact Nat.add_le_add_left Finset.card_image_le w

private theorem parameters {b:ℕ} (hb : 2≤b) {ε:ℝ} (he : 0<ε) :
    ∃ w : ℕ, ∃ q : ℝ, 0<q ∧ q<1 ∧ ((b:ℝ)^w+1)/(q*(b:ℝ)^w)-1≤ε := by
  obtain ⟨w,hw⟩ := exists_nat_gt (2/ε)
  let q := (1+ε/2)/(1+ε)
  have positive : 0<q := by dsimp [q];positivity
  have small : q<1 := by dsimp [q]; apply (div_lt_one (by positivity)).mpr;linarith
  have growNat : w≤b^w := (Nat.lt_two_pow_self (n := w)).le.trans (Nat.pow_le_pow_left hb _)
  have grow : (w:ℝ)≤(b:ℝ)^w := by exact_mod_cast growNat
  have B : 0<(b:ℝ)^w := by positivity
  have two : 2≤ε*(b:ℝ)^w := by
    have h := (div_lt_iff₀ he).mp (hw.trans_le grow)
    linarith only [h]
  refine ⟨w,q,positive,small,?_⟩
  apply sub_le_iff_le_add.mpr
  apply (div_le_iff₀ (mul_pos positive B)).mpr
  dsimp only [q]
  have eq : (ε+1)*((1+ε/2)/(1+ε)*(b:ℝ)^w)=(1+ε/2)*(b:ℝ)^w := by
    field_simp;ring
  rw [eq]
  linarith only [two]

theorem exceptional_sqrt_bound {b:ℕ} (hb : 2≤b) {ε:ℝ} (he : 0<ε) :
    ∃ C:ℝ, 0<C ∧ ∀ k:ℕ, 3≤k → ∀ J:ℕ, 1≤J → ((exceptionalEnds k b J ε).card:ℝ) ≤ C*Real.sqrt J := by
  obtain ⟨w,q,hq,hs,ht⟩ := parameters hb he
  let A : ℝ := 4*w*Real.sqrt (((w:ℝ)+1)*Real.log b)/(-Real.log q)
  have den : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hs)
  have A0 : 0≤A := by dsimp [A]; positivity
  refine ⟨w+A+1,by positivity,?_⟩
  intro k hk J hJ
  have count : ((exceptionalEnds k b J ε).card:ℝ) ≤ (w:ℝ)+(badProfiles k b w J q).card := by
    exact_mod_cast shift_count ht
  have bd := uniform_profile_count hk hb w J hq hs
  have jl : 1≤(J:ℝ) := by exact_mod_cast hJ
  have growJ : (w:ℝ) ≤ (w:ℝ)*J := by nlinarith only [mul_nonneg (Nat.cast_nonneg w (α := ℝ)) (sub_nonneg.mpr jl)]
  have lb : 0≤Real.log b := Real.log_nonneg (by exact_mod_cast (show 1≤b by omega))
  have bound : Real.sqrt (((J+w:ℕ):ℝ)*Real.log b) ≤
      Real.sqrt J*Real.sqrt (((w:ℝ)+1)*Real.log b) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg J)]
    apply Real.sqrt_le_sqrt
    rw [Nat.cast_add]
    have nc := mul_le_mul_of_nonneg_right (show (J:ℝ)+w ≤ (J:ℝ)*((w:ℝ)+1) by linarith only [growJ]) lb
    linarith only [nc]
  have b2 : (badProfiles k b w J q).card ≤ A*Real.sqrt J := by
    apply bd.trans
    have c := mul_le_mul_of_nonneg_left bound (by positivity : 0≤(w:ℝ)*4)
    dsimp only [A]
    have divided := div_le_div_of_nonneg_right c den.le
    calc
      _ ≤ ((w:ℝ)*4*(Real.sqrt J*Real.sqrt (((w:ℝ)+1)*Real.log b)))/(-Real.log q) := by
        simpa only [mul_assoc] using divided
      _ = _ := by ring
  have sqrt1 : 1≤Real.sqrt J := by simpa using Real.sqrt_le_sqrt jl
  have wr := mul_le_mul_of_nonneg_left sqrt1 (Nat.cast_nonneg w (α := ℝ))
  nlinarith only [count,b2,wr,Real.sqrt_nonneg (J:ℝ)]

theorem profile_density_one {k b:ℕ} (hk : 3≤k) (hb : 2≤b) {ε:ℝ} (he : 0<ε) :
    Tendsto (fun J:ℕ => ((exceptionalEnds k b J ε).card:ℝ)/J) atTop (𝓝 0) := by
  obtain ⟨C,_,bd⟩ := exceptional_sqrt_bound hb he
  have limit : Tendsto (fun J:ℕ => C / Real.sqrt J) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop C
  apply squeeze_zero' _ _ limit
  · exact Filter.Eventually.of_forall fun _ => by positivity
  · filter_upwards [eventually_ge_atTop 1] with J hJ
    have jp : 0<(J:ℝ) := by exact_mod_cast (show 0<J by omega)
    have sp := Real.sqrt_pos.mpr jp
    apply (div_le_div_iff₀ jp sp).mpr
    have hbnd := mul_le_mul_of_nonneg_right (bd k hk J hJ) sp.le
    nlinarith only [hbnd,congrArg (C*·) (Real.mul_self_sqrt jp.le)]

#print axioms exceptional_sqrt_bound
#print axioms profile_density_one
end ProgressionParity
