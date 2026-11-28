import RegularScales

namespace ProgressionParity
open Set.IsAPOfLengthFree
open scoped BigOperators

private noncomputable def deficit (k b j : ℕ) : ℝ :=
  Real.log ((b:ℝ)^j) - Real.log (maxCard k (b^j))

private lemma value_pos {k : ℕ} (hk : 3≤k) {N : ℕ} (hn : 0<N) :
    0<(maxCard k N : ℝ) := by
  have lower := interval_mono (by omega : 1<k) (show 1≤N from hn)
  rw [(initial_values (by omega : 1<k)).1 1 (by omega)] at lower
  exact_mod_cast (show 0<maxCard k N by omega)

private lemma deficit_mono {k b : ℕ} (hk : 3≤k) (hb : 2≤b) : Monotone (deficit k b) := by
  apply monotone_nat_of_le_succ
  intro j
  have bpos : 0<(b:ℝ) := by exact_mod_cast (show 0<b by omega)
  have R := value_pos hk (pow_pos (show 0<b by omega) j)
  have S := value_pos hk (pow_pos (show 0<b by omega) (j+1))
  have upper : (maxCard k (b^(j+1)):ℝ) ≤ (b:ℝ)*maxCard k (b^j) := by
    rw [pow_succ,Nat.mul_comm (b^j) b]
    exact_mod_cast multiple_upper (by omega : 1<k) b (b^j)
  have L := Real.log_le_log S upper
  rw [Real.log_mul bpos.ne' R.ne'] at L
  dsimp only [deficit]
  rw [pow_succ,Real.log_mul (pow_pos bpos j).ne' bpos.ne']
  linarith

private lemma deficit_cap {k b : ℕ} (hk : 3≤k) (hb : 2≤b) (j : ℕ) :
    deficit k b j ≤ 4*Real.sqrt ((j:ℝ)*Real.log b) := by
  have hp : 0<(b:ℝ)^j := by positivity
  have natBound := (roth_le_upstream (b^j)).trans (length_mono (by decide : 1<3) hk (b^j))
  have rb : (rothNumberNat (b^j):ℝ) ≤ (maxCard k (b^j):ℝ) := by exact_mod_cast natBound
  have lower := (Behrend.roth_lower_bound (N := b^j)).trans rb
  rw [Nat.cast_pow,Real.log_pow] at lower
  have logged := Real.log_le_log (mul_pos hp (Real.exp_pos _)) lower
  rw [Real.log_mul hp.ne' (Real.exp_pos _).ne',Real.log_exp] at logged
  dsimp only [deficit]
  linarith only [logged]

private lemma sliding_sum (F : ℕ → ℝ) (J w : ℕ) :
    ∑ j ∈ Finset.range J, (F (j+w)-F j) = ∑ i ∈ Finset.range w, (F (J+i)-F i) := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [Finset.sum_range_succ,← ih]
    have tel : ∑ j ∈ Finset.range J, (F ((j+w)+1)-F (j+w)) = F (J+w)-F w := by
      clear ih
      induction J with
      | zero => simp
      | succ J h => rw [Finset.sum_range_succ,h]; simp only [Nat.succ_add]; ring
    rw [← tel,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Nat.add_assoc]
    ring

noncomputable def slowWindows (k b w J : ℕ) (q : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range J).filter (fun j =>
    (maxCard k (b^(j+w)):ℝ) ≤ q*(b:ℝ)^w*maxCard k (b^j))

theorem slow_window_count {k b : ℕ} (hk : 3≤k) (hb : 2≤b) (w J : ℕ)
    {q : ℝ} (hq : 0<q) (hq' : q<1) :
    ((slowWindows k b w J q).card : ℝ) ≤
      w*(4*Real.sqrt (((J+w:ℕ):ℝ)*Real.log b))/(-Real.log q) := by
  classical
  let F := deficit k b
  have fm : Monotone F := deficit_mono hk hb
  have zero : F 0=0 := by simp [F,deficit,(initial_values (by omega : 1<k)).1 1 (by omega)]
  have B : 0<(b:ℝ) := by exact_mod_cast (show 0<b by omega)
  have step {j : ℕ} (hs : j ∈ slowWindows k b w J q) : -Real.log q ≤ F (j+w)-F j := by
    have lhs := value_pos hk (pow_pos (show 0<b by omega) (j+w))
    have rhs := value_pos hk (pow_pos (show 0<b by omega) j)
    have logineq := Real.log_le_log lhs (Finset.mem_filter.mp hs).2
    rw [Real.log_mul (mul_pos hq (pow_pos B w)).ne' rhs.ne',Real.log_mul hq.ne' (pow_pos B w).ne'] at logineq
    dsimp only [F,deficit]
    rw [pow_add,Real.log_mul (pow_pos B j).ne' (pow_pos B w).ne']
    linarith only [logineq]
  apply (le_div_iff₀ (neg_pos.mpr (Real.log_neg hq hq'))).mpr
  calc
    _ = ∑ _j ∈ slowWindows k b w J q, -Real.log q := by simp
    _ ≤ ∑ j ∈ slowWindows k b w J q, (F (j+w)-F j) := Finset.sum_le_sum fun _ hj => step hj
    _ ≤ ∑ j ∈ Finset.range J, (F (j+w)-F j) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => sub_nonneg.mpr (fm (by omega)))
    _ = _ := sliding_sum F J w
    _ ≤ ∑ _i ∈ Finset.range w, F (J+w) := by
      apply Finset.sum_le_sum
      intro i hi
      have lt := Finset.mem_range.mp hi
      have low := fm (show 0 ≤ i by omega)
      have high := fm (show J+i ≤ J+w by omega)
      linarith
    _ ≤ _ := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_left (deficit_cap hk hb (J+w)) (by positivity)

private lemma mesh_upper {k H : ℕ} (hk : 3≤k) (hh : 0<H) (i : ℕ) :
    H*maxCard k i ≤ (i+H)*maxCard k H := by
  have fit := (Nat.lt_mul_div_succ i hh).le
  have m := interval_mono (by omega : 1<k) fit
  rw [Nat.mul_comm H (i/H+1)] at m
  have u := m.trans (multiple_upper (by omega : 1<k) (i/H+1) H)
  have d : H*(i/H+1) ≤ i+H := by
    rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm H (i/H)]
    exact Nat.add_le_add_right (Nat.div_mul_le_self i H) H
  exact (Nat.mul_le_mul_left H u).trans (by simpa only [← Nat.mul_assoc] using Nat.mul_le_mul_right (maxCard k H) d)

theorem block_profile {k B H : ℕ} (hk : 3≤k) (hb : 0<B) (hh : 0<H) {X : ℕ} (hx : X≤B*H) :
    |(maxCard k X:ℝ)/maxCard k (B*H)-(X:ℝ)/(B*H:ℕ)| ≤
      (((B:ℝ)+1)*maxCard k H-maxCard k (B*H))/maxCard k (B*H) := by
  let S : ℝ := maxCard k H
  let R : ℝ := maxCard k (B*H)
  let T : ℝ := (B*H:ℕ)
  let E : ℝ := (B:ℝ)*S-R
  have rp : 0<R := value_pos hk (Nat.mul_pos hb hh)
  have tp : 0<T := by dsimp [T];positivity
  have t : T=(B:ℝ)*H := by simp [T]
  have en : 0≤E := by
    apply sub_nonneg.mpr
    dsimp only [R,S]
    exact_mod_cast multiple_upper (by omega : 1<k) B H
  have upper (i : ℕ) (hi : i≤B*H) :
      T*(maxCard k i:ℝ)-(i:ℝ)*R ≤ T*(S+E) := by
    have mesh : (H:ℝ)*maxCard k i ≤ ((i:ℝ)+H)*S := by dsimp only [S];exact_mod_cast mesh_upper hk hh i
    have h := mul_le_mul_of_nonneg_left mesh (by positivity : 0≤(B:ℝ))
    have it : (i:ℝ) ≤ T := by dsimp only [T];exact_mod_cast hi
    have left := mul_le_mul_of_nonneg_right it en
    dsimp only [E] at left ⊢
    rw [t] at left ⊢
    linarith only [h,left]
  have up := upper X hx
  have tail := upper (B*H-X) (Nat.sub_le _ _)
  rw [Nat.cast_sub hx] at tail
  have sub : R ≤ (maxCard k X:ℝ)+maxCard k (B*H-X) := by
    have add := interval_subadditive (by omega : 1<k) X (B*H-X)
    rw [Nat.add_sub_of_le hx] at add
    dsimp only [R]
    exact_mod_cast add
  have scaled := mul_le_mul_of_nonneg_left sub tp.le
  have raw : |T*(maxCard k X:ℝ)-(X:ℝ)*R| ≤ T*(S+E) := by
    apply abs_le.mpr
    constructor
    · change T*(maxCard k (B*H-X):ℝ)-(T-X)*R ≤ _ at tail
      linarith only [scaled,tail]
    · exact up
  change |(maxCard k X:ℝ)/R-(X:ℝ)/T| ≤ (((B:ℝ)+1)*S-R)/R
  have id : (maxCard k X:ℝ)/R-(X:ℝ)/T=(T*(maxCard k X:ℝ)-(X:ℝ)*R)/(R*T) := by
    field_simp
  rw [id,abs_div,abs_of_pos (mul_pos rp tp)]
  calc
    _ ≤ T*(S+E)/(R*T) := div_le_div_of_nonneg_right raw (mul_pos rp tp).le
    _ = _ := by dsimp [E];field_simp;ring

/-- Window starts whose normalized profile is outside the tolerance at some integer position. -/
noncomputable def badProfiles (k b w J : ℕ) (q : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range J).filter (fun j => ∃ x ≤ b^(j+w),
    ((b:ℝ)^w+1)/(q*(b:ℝ)^w)-1 <
      |(maxCard k x:ℝ)/maxCard k (b^(j+w))-(x:ℝ)/(b^(j+w):ℕ)|)

theorem uniform_profile_count {k b : ℕ} (hk : 3≤k) (hb : 2≤b) (w J : ℕ)
    {q : ℝ} (hq : 0<q) (hq' : q<1) :
    ((badProfiles k b w J q).card:ℝ) ≤
      w*(4*Real.sqrt (((J+w:ℕ):ℝ)*Real.log b))/(-Real.log q) := by
  classical
  suffices sub : badProfiles k b w J q ⊆ slowWindows k b w J q by
    exact (show ((badProfiles k b w J q).card:ℝ) ≤ (slowWindows k b w J q).card by
      exact_mod_cast Finset.card_le_card sub).trans (slow_window_count hk hb w J hq hq')
  intro j hj
  obtain ⟨inJ,x,hx,fail⟩ := Finset.mem_filter.mp hj
  apply Finset.mem_filter.mpr
  refine ⟨inJ, ?_⟩
  by_contra! good
  let B := b^w
  let H := b^j
  have id : B*H=b^(j+w) := by rw [pow_add,Nat.mul_comm]
  have bp : 0<B := pow_pos (by omega : 0<b) _
  have hp : 0<H := pow_pos (by omega : 0<b) _
  have bp' : 0<(B:ℝ) := by exact_mod_cast bp
  have rp := value_pos hk (Nat.mul_pos bp hp)
  have qr := mul_pos hq bp'
  have endbound : q*(B:ℝ)*(maxCard k H:ℝ) ≤ (maxCard k (B*H):ℝ) := by
    rw [id]
    dsimp [B,H]
    rw [Nat.cast_pow]
    exact good.le
  have prof := block_profile hk bp hp (X := x) (id.symm ▸ hx)
  have cap : (((B:ℝ)+1)*maxCard k H-maxCard k (B*H))/maxCard k (B*H) ≤
      ((B:ℝ)+1)/(q*(B:ℝ))-1 := by
    rw [sub_div,div_self rp.ne',sub_le_sub_iff_right,div_le_div_iff₀ rp qr]
    have key := mul_le_mul_of_nonneg_left endbound (by positivity : 0≤(B:ℝ)+1)
    linarith only [key]
  have ok := prof.trans cap
  rw [id] at ok
  dsimp only [B] at ok
  simp only [Nat.cast_pow] at ok fail
  exact (not_lt_of_ge ok) fail

#print axioms slow_window_count
#print axioms block_profile
#print axioms uniform_profile_count
end ProgressionParity
