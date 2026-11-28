import Density

namespace ProgressionParity
open Set.IsAPOfLengthFree
open scoped BigOperators
open Filter Topology

def badEndpoint (k N : ℕ) (ε : ℝ) : Prop := ∃ x ≤ N,
    ε < |(maxCard k x:ℝ)/maxCard k N-(x:ℝ)/N|

private lemma max_pos {k n : ℕ} (hk : 3≤k) (hn : 0<n) : 0<(maxCard k n:ℝ) := by
  have le := interval_mono (by omega : 1<k) (show 1≤n from hn)
  rw [(initial_values (by omega : 1<k)).1 1 (by omega)] at le
  exact_mod_cast (show 0<maxCard k n by omega)

private lemma transfer {k N M : ℕ} (hk : 3≤k) (hn : 0<N) (inside : N≤M) (half : M≤2*N)
    {ε δ : ℝ} (small : δ≤1/4) (tol : 8*δ≤ε) :
    badEndpoint k N ε → badEndpoint k M δ := by
  rintro ⟨x,hx,bad⟩
  by_contra good
  have ok {i:ℕ} (hi : i≤M) : |(maxCard k i:ℝ)/maxCard k M-(i:ℝ)/M| ≤ δ := by
    exact le_of_not_gt (fun f => good ⟨i,hi,f⟩)
  let a : ℝ := (maxCard k x:ℝ)/maxCard k M
  let v : ℝ := (maxCard k N:ℝ)/maxCard k M
  let u : ℝ := (x:ℝ)/N
  let t : ℝ := (N:ℝ)/M
  have rp := max_pos hk (show 0<M by omega)
  have np : 0<(N:ℝ) := by exact_mod_cast hn
  have mp : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have vp : 0<v := div_pos (max_pos hk hn) rp
  have up : 0≤u := by dsimp [u];positivity
  have us : u≤1 := (div_le_one np).mpr (by exact_mod_cast hx)
  have ts : 1/2≤t := by
    apply (le_div_iff₀ mp).mpr
    have h : (M:ℝ)≤2*N := by exact_mod_cast half
    linarith
  have guard : |v-t|≤δ := ok inside
  have vt := abs_le.mp guard
  have vlow : 1/4≤v := by linarith
  have ut : u*t=(x:ℝ)/M := by dsimp [u,t]; field_simp
  have err : |a-u*t|≤δ := by rw [ut];exact ok (hx.trans inside)
  have zero : 0≤δ := (abs_nonneg _).trans guard
  have total : |a-u*v|≤2*δ := by
    calc
      _ = |(a-u*t)+u*(t-v)| := by congr 1;ring
      _ ≤ |a-u*t|+|u*(t-v)| := abs_add_le _ _
      _ ≤ δ+δ := by
        apply add_le_add err
        rw [abs_mul,abs_of_nonneg up,abs_sub_comm]
        exact (mul_le_mul_of_nonneg_left guard up).trans (by simpa using mul_le_mul_of_nonneg_right us zero)
      _ = _ := by ring
  have factor : (maxCard k x:ℝ)/maxCard k N-u=(a-u*v)/v := by
    have nonzero := (max_pos hk hn).ne'
    dsimp only [a,v]
    field_simp [nonzero]
  have upper : |(maxCard k x:ℝ)/maxCard k N-u|≤ε := by
    rw [factor,abs_div,abs_of_pos vp]
    apply (div_le_iff₀ vp).mpr
    have epos : 0≤ε := by linarith
    have mul := mul_le_mul_of_nonneg_left vlow epos
    linarith only [total,tol,mul]
  exact (not_lt_of_ge upper) bad

noncomputable def badWeight (k n : ℕ) (ε:ℝ) : ℝ := by
  classical
  exact if badEndpoint k n ε then (n:ℝ)⁻¹ else 0

noncomputable def logMass (k X : ℕ) (ε:ℝ) : ℝ := ∑ n ∈ Finset.range X, badWeight k n ε

private lemma weight_bounds (k n : ℕ) (ε:ℝ) : 0≤badWeight k n ε ∧ badWeight k n ε≤(n:ℝ)⁻¹ := by
  classical
  unfold badWeight
  split <;> simp [inv_nonneg.mpr (Nat.cast_nonneg n (α := ℝ))]

private lemma mass_dyadic {k : ℕ} (hk : 3≤k) (J:ℕ) {ε δ:ℝ}
    (small : δ≤1/4) (tol : 8*δ≤ε) :
    logMass k (2^J) ε ≤ ((exceptionalEnds k 2 (J+1) δ).card:ℝ) := by
  classical
  induction J with
  | zero =>
    simp only [pow_zero,logMass,Finset.sum_range_one]
    exact (by simpa using (weight_bounds k 0 ε).2 : badWeight k 0 ε ≤ 0) |>.trans (Nat.cast_nonneg _)
  | succ J ih =>
    let M := 2^J
    have hp : 0<M := pow_pos (by decide : 0<2) J
    have id : 2^(J+1)=M+M := by rw [pow_succ];dsimp only [M];omega
    have split : logMass k (2^(J+1)) ε=logMass k M ε+∑ i ∈ Finset.range M, badWeight k (M+i) ε := by
      rw [id];exact Finset.sum_range_add _ _ _
    rw [split]
    by_cases bad : badEndpoint k (2^(J+1)) δ
    · have sc : exceptionalEnds k 2 (J+1+1) δ=insert (J+1) (exceptionalEnds k 2 (J+1) δ) := by
        simpa [exceptionalEnds,Finset.range_add_one,Finset.filter_insert,badEndpoint] using
          (if_pos bad : (if badEndpoint k (2^(J+1)) δ then insert (J+1) (exceptionalEnds k 2 (J+1) δ)
            else exceptionalEnds k 2 (J+1) δ)=_)
      have absent : J+1 ∉ exceptionalEnds k 2 (J+1) δ := by simp [exceptionalEnds]
      rw [sc,Finset.card_insert_of_notMem absent,Nat.cast_add_one]
      apply add_le_add ih
      calc
        _ ≤ ∑ _i ∈ Finset.range M, (M:ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro i hi
          apply (weight_bounds _ _ _).2.trans
          exact inv_anti₀ (by exact_mod_cast hp : 0<(M:ℝ)) (by exact_mod_cast (show M≤M+i by omega))
        _ = 1 := by simp [show (M:ℝ)≠0 by exact_mod_cast hp.ne']
    · have sc : exceptionalEnds k 2 (J+1+1) δ=exceptionalEnds k 2 (J+1) δ := by
        simpa [exceptionalEnds,Finset.range_add_one,Finset.filter_insert,badEndpoint] using
          (if_neg bad : (if badEndpoint k (2^(J+1)) δ then insert (J+1) (exceptionalEnds k 2 (J+1) δ)
            else exceptionalEnds k 2 (J+1) δ)=_)
      have none : ∑ i ∈ Finset.range M, badWeight k (M+i) ε=0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have lt := Finset.mem_range.mp hi
        have no := mt (transfer hk (show 0<M+i by omega) (show M+i≤2^(J+1) by rw [id];omega)
          (show 2^(J+1)≤2*(M+i) by rw [id];omega) small tol) bad
        simp [badWeight,no]
      rw [sc,none,add_zero]
      exact ih

theorem logarithmic_mass_bound {ε:ℝ} (he : 0<ε) :
    ∃ C:ℝ, 0<C ∧ ∀ k:ℕ, 3≤k → ∀ X:ℕ, 2≤X →
      logMass k X ε ≤ C*Real.sqrt (Real.log X) := by
  let δ : ℝ := min (ε/8) (1/4)
  have dp : 0<δ := lt_min (by positivity) (by norm_num)
  obtain ⟨C,cp,bd⟩ := exceptional_sqrt_bound (b := 2) (by decide) dp
  have two : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C*Real.sqrt (3/Real.log 2),by positivity,?_⟩
  intro k hk X hx
  let j := X.log2
  have xp : X≠0 := by omega
  have left : 2^j≤X := (Nat.le_log2 xp).mp le_rfl
  have right : X<2^(j+1) := (Nat.log2_lt xp).mp (by dsimp [j];omega)
  have jp : 1≤j := (Nat.le_log2 xp).mpr (by simpa using hx)
  have logx : (j:ℝ)*Real.log 2≤Real.log X := by
    have h : (2:ℝ)^j ≤ (X:ℝ) := by exact_mod_cast left
    have z := Real.log_le_log (by positivity : 0<(2:ℝ)^j) h
    rwa [Real.log_pow] at z
  have small : δ≤1/4 := min_le_right _ _
  have tol : 8*δ≤ε := by have h : δ≤ε/8 := min_le_left _ _;linarith
  have mass : logMass k X ε ≤ logMass k (2^(j+1)) ε := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono right.le)
    exact fun n _ _ => (weight_bounds k n ε).1
  have d := mass.trans (mass_dyadic hk (j+1) small tol)
  have upper := d.trans (bd k hk (j+1+1) (by omega))
  have compare : (((j+1+1:ℕ):ℝ))≤3/Real.log 2*Real.log X := by
    have jpos : 1≤(j:ℝ) := by exact_mod_cast jp
    rw [div_mul_eq_mul_div,le_div_iff₀ two]
    push_cast
    have h := mul_le_mul_of_nonneg_right (show (j:ℝ)+1+1≤3*j by linarith) two.le
    linarith only [h,logx]
  have z := Real.sqrt_le_sqrt compare
  rw [Real.sqrt_mul (by positivity : 0≤3/Real.log 2)] at z
  exact upper.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left z cp.le)

theorem logarithmic_density_one {k:ℕ} (hk : 3≤k) {ε:ℝ} (he : 0<ε) :
    Tendsto (fun X:ℕ => logMass k X ε/Real.log X) atTop (𝓝 0) := by
  obtain ⟨C,_,bd⟩ := logarithmic_mass_bound he
  have tends := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have lim : Tendsto (fun X:ℕ => C/Real.sqrt (Real.log X)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp tends).const_div_atTop C
  apply squeeze_zero' _ _ lim
  · filter_upwards [eventually_ge_atTop 2] with X hx
    have pos := Real.log_pos (show 1<(X:ℝ) by exact_mod_cast (show 1<X by omega))
    exact div_nonneg (Finset.sum_nonneg fun n _ => (weight_bounds k n ε).1) pos.le
  · filter_upwards [eventually_ge_atTop 2] with X hx
    have pos := Real.log_pos (show 1<(X:ℝ) by exact_mod_cast (show 1<X by omega))
    have sp := Real.sqrt_pos.mpr pos
    apply (div_le_div_iff₀ pos sp).mpr
    have h := mul_le_mul_of_nonneg_right (bd k hk X hx) sp.le
    nlinarith only [h,congrArg (C*·) (Real.mul_self_sqrt pos.le)]

#print axioms logarithmic_mass_bound
#print axioms logarithmic_density_one
end ProgressionParity
