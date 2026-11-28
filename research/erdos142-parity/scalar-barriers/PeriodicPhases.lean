import Mathlib

/-! # Uniform limits on adaptive phases of periodic Roth substitutions

Credit: @Deldor14. The moving-window estimate specializes and extends the
single-step Behrend argument in the companion RegularScales.lean.
-/

namespace Erdos142PhaseWeights
open Finset

private theorem multiples_bound (b n : ℕ) : rothNumberNat (b*n) ≤ b*rothNumberNat n := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.succ_mul,Nat.succ_mul]
    exact (rothNumberNat_add_le _ _).trans (Nat.add_le_add_right ih _)

/-- Each residue class of a free input on qm sites has at most R(m) points. -/
theorem one_class {q m : ℕ} (qp : 0<q) (A : Finset ℕ) (bound : A ⊆ range (q*m))
    (free : ThreeAPFree (A:Set ℕ)) (r : ℕ) :
    (A.filter (fun x => x%q=r)).card ≤ rothNumberNat m := by
  classical
  let C:=A.filter (fun x=>x%q=r)
  let T:=C.image (fun x=>x/q)
  have mem {x} (h : x∈C) : x∈A ∧ x%q=r := Finset.mem_filter.mp h
  have rep {x} (hx : x∈C) : q*(x/q)+r=x := (mem hx).2 ▸ Nat.div_add_mod x q
  have inj : (C:Set ℕ).InjOn (fun x=>x/q) := by
    intro x hx y hy eq
    have a:=rep hx
    have b:=rep hy
    change x/q=y/q at eq
    rw [eq] at a
    omega
  have top : T ⊆ range m := by
    intro y hy
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
    exact mem_range.mpr ((Nat.div_lt_iff_lt_mul qp).mpr (by simpa [Nat.mul_comm] using mem_range.mp (bound (mem hx).1)))
  have tf : ThreeAPFree (T:Set ℕ) := by
    apply threeAPFree_iff_eq_right.mpr
    intro u hu v hv w hw eq
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hu
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hv
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hw
    have orig : x+z=y+y := by
      calc x+z = (q*(x/q)+r)+(q*(z/q)+r) := congrArg₂ (·+·) (rep hx).symm (rep hz).symm
           _ = q*(x/q+z/q)+(r+r) := by ring
           _ = (q*(y/q)+r)+(q*(y/q)+r) := by rw [eq]; ring
           _ = y+y := by rw [rep hy]
    have col:=threeAPFree_iff_eq_right.mp free (mem hx).1 (mem hy).1 (mem hz).1 orig
    rw [col]
  calc
    _ = T.card := (Finset.card_image_of_injOn inj).symm
    _ ≤ _ := ThreeAPFree.le_rothNumberNat T tf (fun _ hx => mem_range.mp (top hx)) rfl

/-- Enumeration of outputs congruent to r in the output period, paired with their
unique input coordinate. It permits arbitrary labels and arbitrary translations. -/
def outputPairs {p : ℕ} (D : Finset (ZMod p)) (f : ZMod p → ℤ)
    (q : ℕ) (A : Finset ℕ) (shift : ℤ) : Finset ((_r : ZMod p) × ℕ) :=
  D.sigma fun r => A.filter (fun x => x%q=((f r-shift:ℤ):ZMod q).val)

theorem uniform_output_bound {q b m p : ℕ} (qp : 0<q)
    (A : Finset ℕ) (bound : A ⊆ range ((q*b)*m)) (free : ThreeAPFree (A:Set ℕ))
    (D : Finset (ZMod p)) (f : ZMod p → ℤ) (shift : ℤ) :
    (outputPairs D f q A shift).card ≤ D.card*b*rothNumberNat m := by
  classical
  rw [outputPairs,Finset.card_sigma]
  have cap (r : ZMod p) :=
    (one_class qp A (show A ⊆ range (q*(b*m)) by simpa [Nat.mul_assoc] using bound)
      free ((f r-shift:ℤ):ZMod q).val).trans (multiples_bound b m)
  calc _ ≤ ∑ _r ∈ D, b*rothNumberNat m := Finset.sum_le_sum fun r _ => cap r
       _ = _ := by simp [Nat.mul_assoc]

/-- Every actual output position has a distinct canonical pair, including for
negative positions or shifts and arbitrarily distant labels. -/
theorem actual_output_le_pairs {q p : ℕ} (qp : 0<q) (pp : 0<p)
    (A : Finset ℕ) (D : Finset (ZMod p)) (f : ZMod p → ℤ) (shift : ℤ) (O : Finset ℤ)
    (out : ∀ u ∈ O, (u:ZMod p) ∈ D ∧ ∃ a ∈ A, f (u:ZMod p)+(u/(p:ℤ))*q=(a:ℤ)+shift) :
    O.card ≤ (outputPairs D f q A shift).card := by
  classical
  have : NeZero p:=⟨pp.ne'⟩
  have : NeZero q:=⟨qp.ne'⟩
  let L:=fun u:ℤ => f (u:ZMod p)+(u/(p:ℤ))*q-shift
  let code:=fun u:ℤ => (⟨(u:ZMod p),(L u).toNat⟩ : (_r:ZMod p) × ℕ)
  have input {u : ℤ} (hu : u ∈ O) : ∃ a ∈ A, L u=(a:ℤ) := by
    obtain ⟨a,ha,h⟩:=(out u hu).2
    exact ⟨a,ha,by dsimp [L]; omega⟩
  apply Finset.card_le_card_of_injOn code
  · intro u hu
    obtain ⟨a,ha,h⟩:=input hu
    apply Finset.mem_sigma.mpr
    refine ⟨(out u hu).1,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
    · simpa [code,h] using ha
    · change (L u).toNat % q = _
      rw [h,Int.toNat_natCast]
      have cast := congrArg (fun v:ℤ => (v:ZMod q)) h
      simp [L] at cast
      simpa [ZMod.val_natCast,code,Int.cast_sub] using congrArg ZMod.val cast.symm
  · intro u hu v hv eq
    have res:=congrArg Sigma.fst eq
    have ix:=congrArg (fun c : (_r:ZMod p) × ℕ => c.2) eq
    change (u:ZMod p)=(v:ZMod p) at res
    change (L u).toNat=(L v).toNat at ix
    obtain ⟨a,ha,ea⟩:=input hu
    obtain ⟨b,hb,eb⟩:=input hv
    rw [ea,eb] at ix
    simp only [Int.toNat_natCast] at ix
    subst b
    have same:=ea.trans eb.symm
    dsimp [L] at same
    rw [res] at same
    have prod : (u/(p:ℤ))*(q:ℤ)=(v/(p:ℤ))*q := by omega
    have div: u/(p:ℤ)=v/(p:ℤ) := mul_right_cancel₀ (by exact_mod_cast qp.ne') prod
    have rem: u%(p:ℤ)=v%(p:ℤ) := (ZMod.intCast_eq_intCast_iff' u v p).mp res
    have x:=Int.emod_add_ediv_mul u (p:ℤ)
    have y:=Int.emod_add_ediv_mul v (p:ℤ)
    rw [div,rem] at x
    omega

/-- A rounded estimate requiring no divisibility between the input period and the
observation scale. This controls every input phase at once. -/
theorem rounded_window {j M q p : ℕ} (qp : 0 < q) (pp : 0 < p)
    (A : Finset ℕ) (bound : A ⊆ range (2^(j+M))) (free : ThreeAPFree (A:Set ℕ))
    (D : Finset (ZMod p)) (f : ZMod p → ℤ) (shift : ℤ) (O : Finset ℤ)
    (out : ∀ u ∈ O, (u:ZMod p) ∈ D ∧ ∃ a ∈ A, f (u:ZMod p)+(u/(p:ℤ))*q=(a:ℤ)+shift) :
    q*O.card ≤ D.card*(2^M+q)*rothNumberNat (2^j) := by
  let b:=(2^M-1)/q+1
  have ppow : 0 < 2^M := pow_pos (by decide) _
  have rem:=Nat.div_add_mod (2^M-1) q
  have lt:=Nat.mod_lt (2^M-1) qp
  have low : 2^M ≤ q*b := by dsimp [b];rw [Nat.mul_add,Nat.mul_one];omega
  have high : q*b ≤ 2^M+q := by dsimp [b];rw [Nat.mul_add,Nat.mul_one];omega
  have fit : A ⊆ range ((q*b)*2^j) := by
    apply bound.trans
    apply Finset.range_mono
    rw [pow_add,Nat.mul_comm (2^j)]
    exact Nat.mul_le_mul_right (2^j) low
  have hb := (actual_output_le_pairs qp pp A D f shift O out).trans (uniform_output_bound qp A fit free D f shift)
  calc q*O.card ≤ q*(D.card*b*rothNumberNat (2^j)) := Nat.mul_le_mul_left q hb
       _ = D.card*(q*b)*rothNumberNat (2^j) := by ring
       _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ high)

private theorem cover_steps (n d : ℕ) (dp : 0 < d) :
    n ≤ d*(n/d+1) ∧ d*(n/d+1) ≤ n+d := by
  have rem:=Nat.div_add_mod n d
  have lt:=Nat.mod_lt n dp
  rw [Nat.mul_add,Nat.mul_one]
  omega

private theorem scaled_R (n L : ℕ) (lp : 0 < L) :
    L*rothNumberNat n ≤ (n+L)*rothNumberNat L := by
  obtain ⟨low,high⟩:=cover_steps n L lp
  have fit:=rothNumberNat.monotone low
  rw [Nat.mul_comm L] at fit
  have cap:=fit.trans (multiples_bound _ L)
  calc _ ≤ L*((n/L+1)*rothNumberNat L) := Nat.mul_le_mul_left _ cap
       _ = (L*(n/L+1))*rothNumberNat L := by ring
       _ ≤ _ := Nat.mul_le_mul_right _ high

/-- Any input length and any mesh of length L. Both the symbol map and the
choice of phase may depend on the input. -/
theorem rounded_interval {N L q p : ℕ} (lp : 0 < L) (qp : 0 < q) (pp : 0 < p)
    (A : Finset ℕ) (bound : A ⊆ range N) (free : ThreeAPFree (A:Set ℕ))
    (D : Finset (ZMod p)) (f : ZMod p → ℤ) (shift : ℤ) (O : Finset ℤ)
    (out : ∀ u ∈ O, (u:ZMod p) ∈ D ∧ ∃ a ∈ A, f (u:ZMod p)+(u/(p:ℤ))*q=(a:ℤ)+shift) :
    L*q*O.card ≤ D.card*(N+q*L)*rothNumberNat L := by
  let b:=N/(q*L)+1
  obtain ⟨low,high⟩:=cover_steps N (q*L) (Nat.mul_pos qp lp)
  have fit : A ⊆ range ((q*b)*L) := by
    apply bound.trans
    apply Finset.range_mono
    calc N ≤ (q*L)*b := low
         _ = _ := by ring
  have hb := (actual_output_le_pairs qp pp A D f shift O out).trans (uniform_output_bound qp A fit free D f shift)
  calc L*q*O.card ≤ L*q*(D.card*b*rothNumberNat L) := Nat.mul_le_mul_left _ hb
       _ = D.card*((q*L)*b)*rothNumberNat L := by ring
       _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ high)

/-- Between the two endpoints K L and L of a regular window, the relative loss
from rounding is uniform even over all intermediate observation lengths. -/
theorem intermediate_bound {K L N q p : ℕ} (lp : 0 < L) (qp : 0 < q) (pp : 0 < p)
    (within : N ≤ K*L) {η : ℝ} (retained : η*K*rothNumberNat L ≤ rothNumberNat (K*L))
    (A : Finset ℕ) (bound : A ⊆ range N) (free : ThreeAPFree (A:Set ℕ))
    (D : Finset (ZMod p)) (f : ZMod p → ℤ) (shift : ℤ) (O : Finset ℤ)
    (out : ∀ u ∈ O, (u:ZMod p) ∈ D ∧ ∃ a ∈ A, f (u:ZMod p)+(u/(p:ℤ))*q=(a:ℤ)+shift) :
    ((N:ℝ)-L-(1-η)*(K*L))*q*O.card ≤ D.card*(N+q*L:ℝ)*rothNumberNat N := by
  have sub:=rothNumberNat_add_le N (K*L-N)
  rw [Nat.add_sub_of_le within] at sub
  have remain := (Nat.mul_le_mul_left L sub).trans_eq (Nat.mul_add _ _ _)
  have tail:=scaled_R (K*L-N) L lp
  have whole : (L:ℝ)*rothNumberNat (K*L) ≤ L*rothNumberNat N+
      (((K*L-N:ℕ):ℝ)+L)*rothNumberNat L := by
    exact_mod_cast remain.trans (Nat.add_le_add_left tail (L*rothNumberNat N))
  rw [Nat.cast_sub within,Nat.cast_mul] at whole
  have lower : ((N:ℝ)-L-(1-η)*(K*L))*rothNumberNat L ≤ L*rothNumberNat N := by
    nlinarith only [whole,mul_le_mul_of_nonneg_left retained (Nat.cast_nonneg L : 0≤(L:ℝ))]
  have upper : (L:ℝ)*q*O.card ≤ D.card*(N+q*L:ℝ)*rothNumberNat L := by
    exact_mod_cast rounded_interval lp qp pp A bound free D f shift O out
  by_cases hp : 0 ≤ (N:ℝ)-L-(1-η)*(K*L)
  · apply (mul_le_mul_iff_right₀ (show 0<(L:ℝ) by exact_mod_cast lp)).mp
    nlinarith only [mul_le_mul_of_nonneg_left upper hp,
      mul_le_mul_of_nonneg_left lower (by positivity : 0≤D.card*(N+q*L:ℝ))]
  · exact (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hp) (Nat.cast_nonneg q))
      (Nat.cast_nonneg O.card)).trans (by positivity)

/-- Summing over all representatives of the input phase gives the exact total,
without assumptions on progressions or injectivity of the input labels. -/
theorem phase_sum {p q : ℕ} [NeZero q] (D : Finset (ZMod p))
    (f : ZMod p → ℤ) (A : Finset ℕ) :
    ∑ s : ZMod q, (outputPairs D f q A (s.val:ℤ)).card = D.card*A.card := by
  classical
  simp only [outputPairs,Finset.card_sigma]
  rw [Finset.sum_comm]
  have one (r : ZMod p) : ∑ s : ZMod q, (A.filter (fun x =>
      x%q=((f r-(s.val:ℤ):ℤ):ZMod q).val)).card = A.card := by
    let F:=fun x:ℕ => (f r:ZMod q)-(x:ZMod q)
    have e (x:ℕ) (s:ZMod q) : x%q=((f r-(s.val:ℤ):ℤ):ZMod q).val ↔ F x=s := by
      rw [←ZMod.val_natCast q x,Int.cast_sub,Int.cast_natCast,ZMod.natCast_zmod_val,
        (ZMod.val_injective q).eq_iff]
      change (x:ZMod q)=(f r:ZMod q)-s ↔ (f r:ZMod q)-x=s
      constructor <;> intro h <;> linear_combination -h
    simp_rw [e]
    simpa using Finset.sum_card_fiberwise_eq_card_filter A (Finset.univ:Finset (ZMod q)) F
  simp_rw [one]
  simp

/-- Each pair contributing to the phase count lifts to one genuine integer
output. Together with the injection in the other direction this realizes the exact count. -/
theorem realize_phase {q p : ℕ} (qp : 0<q) (pp : 0<p) (A : Finset ℕ)
    (D : Finset (ZMod p)) (f : ZMod p → ℤ) (s : ℤ) :
    ∃ O : Finset ℤ, (∀ u ∈ O, (u:ZMod p)∈D ∧ ∃ a∈A, f (u:ZMod p)+(u/(p:ℤ))*q=(a:ℤ)+s)
      ∧ O.card=(outputPairs D f q A s).card := by
  classical
  have : NeZero p:=⟨pp.ne'⟩
  have : NeZero q:=⟨qp.ne'⟩
  let T:=outputPairs D f q A s
  let k:=fun z : (_r:ZMod p) × ℕ => ((z.2:ℤ)+s-f z.1)/(q:ℤ)
  let U:=fun z : (_r:ZMod p) × ℕ => (z.1.val:ℤ)+k z*(p:ℤ)
  have res (z) : (U z:ZMod p)=z.1 := by simp [U]
  have div (z) : U z/(p:ℤ)=k z := by
    dsimp [U]
    rw [Int.add_mul_ediv_right _ _ (by exact_mod_cast pp.ne'),
        Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by exact_mod_cast z.1.val_lt),zero_add]
  have restore {z} (hz : z∈T) : f z.1 + k z*q=(z.2:ℤ)+s := by
    have ma:=(Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2).2
    have m : (z.2:ZMod q)=((f z.1-s:ℤ):ZMod q) := by
      apply ZMod.val_injective
      simpa only [ZMod.val_natCast] using ma
    have dvd : (q:ℤ) ∣ (z.2:ℤ)+s-f z.1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast at m ⊢
      linear_combination m
    have eq:=Int.ediv_mul_cancel dvd
    dsimp [k]
    omega
  refine ⟨T.image U,?_,Finset.card_image_of_injOn ?_⟩
  · intro u hu
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hu
    rw [res,div]
    exact ⟨(Finset.mem_sigma.mp hz).1,z.2,(Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2).1,restore hz⟩
  · intro z hz w hw hu
    have rz : z.1=w.1 := (res _).symm.trans ((congrArg (fun v:ℤ => (v:ZMod p)) hu).trans (res _))
    have kk : k z=k w := (div _).symm.trans ((congrArg (fun v:ℤ => v/(p:ℤ)) hu).trans (div _))
    have first:=restore hz
    rw [rz,kk] at first
    have second:=restore hw
    apply Sigma.ext rz
    apply heq_of_eq
    omega

end Erdos142PhaseWeights

namespace Erdos142ScaleWindows
open Finset

private theorem rep_bound (b m : ℕ) : rothNumberNat (b*m) ≤ b*rothNumberNat m := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.succ_mul,Nat.succ_mul]
    exact (rothNumberNat_add_le _ _).trans (Nat.add_le_add_right ih _)

noncomputable def deficit (j : ℕ) : ℝ :=
  (j:ℝ)*Real.log 2 - Real.log (rothNumberNat (2^j))

private theorem positiveR (j : ℕ) : 0 < (rothNumberNat (2^j):ℝ) := by
  have be:=Behrend.roth_lower_bound (N:=2^j)
  exact lt_of_lt_of_le (by positivity) be

private theorem deficit_nonneg (j : ℕ) : 0 ≤ deficit j := by
  have le : (rothNumberNat (2^j):ℝ) ≤ (2:ℝ)^j := by exact_mod_cast rothNumberNat_le _
  have lg:=Real.log_le_log (positiveR _) le
  rw [Real.log_pow] at lg
  dsimp [deficit];linarith

theorem window_nonneg (j M : ℕ) : 0 ≤ deficit (j+M)-deficit j := by
  have bound : (rothNumberNat (2^(j+M)):ℝ) ≤ (2:ℝ)^M*rothNumberNat (2^j) := by
    exact_mod_cast (show rothNumberNat (2^(j+M)) ≤ 2^M*rothNumberNat (2^j) by
      rw [Nat.add_comm,pow_add]; exact rep_bound _ _)
  have lg:=Real.log_le_log (positiveR _) bound
  rw [Real.log_mul (by positivity) (positiveR _).ne',Real.log_pow] at lg
  dsimp [deficit]
  push_cast
  linarith

theorem deficit_upper (j : ℕ) : deficit j ≤ 4*Real.sqrt ((j:ℝ)*Real.log 2) := by
  have be:=Behrend.roth_lower_bound (N:=2^j)
  rw [Nat.cast_pow] at be
  norm_num only [Nat.cast_ofNat] at be
  have logb:=Real.log_le_log (by positivity) be
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',Real.log_exp,Real.log_pow] at logb
  dsimp [deficit]
  linarith

theorem window_sum (J M : ℕ) :
    ∑ j ∈ range J, (deficit (j+M)-deficit j) ≤ (M:ℝ)*4*Real.sqrt (((J+M):ℕ)*Real.log 2) := by
  have swap : (∑ j ∈ range J, deficit (j+M))+(∑ j ∈ range M, deficit j) =
      (∑ j ∈ range J, deficit j)+(∑ j ∈ range M, deficit (J+j)) := by
    have lhs:=Finset.sum_range_add deficit M J
    have rhs:=Finset.sum_range_add deficit J M
    rw [Nat.add_comm M J] at lhs
    simpa [add_comm] using lhs.symm.trans rhs
  have top : ∑ k ∈ range M, deficit (J+k) ≤ ∑ _k ∈ range M, (4*Real.sqrt (((J+M):ℕ)*Real.log 2)) := by
    apply Finset.sum_le_sum
    intro k hk
    apply (deficit_upper _).trans
    have kk:=mem_range.mp hk
    gcongr
  have nn : 0 ≤ ∑ k ∈ range M, deficit k := Finset.sum_nonneg (fun k _ => deficit_nonneg k)
  simp only [Finset.sum_const,card_range,nsmul_eq_mul] at top
  rw [Finset.sum_sub_distrib]
  linarith

noncomputable def exceptional (J M : ℕ) (δ : ℝ) : Finset ℕ := by
  classical
  exact (range J).filter (fun j => δ < deficit (j+M)-deficit j)

theorem window_count (J M : ℕ) (δ : ℝ) :
    ((exceptional J M δ).card:ℝ)*δ ≤ (M:ℝ)*4*Real.sqrt (((J+M):ℕ)*Real.log 2) := by
  classical
  apply le_trans _ (window_sum J M)
  calc
    _ = ∑ _j ∈ exceptional J M δ, δ := by simp
    _ ≤ ∑ j ∈ exceptional J M δ, (deficit (j+M)-deficit j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Finset.mem_filter.mp hj).2.le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => window_nonneg j M)

theorem regular_ratio {j M : ℕ} {δ : ℝ} (good : deficit (j+M)-deficit j ≤ δ) :
    (2:ℝ)^M*rothNumberNat (2^j) ≤ Real.exp δ*rothNumberNat (2^(j+M)) := by
  apply (Real.log_le_log_iff (mul_pos (pow_pos (by norm_num) _) (positiveR j))
    (mul_pos (Real.exp_pos _) (positiveR (j+M)))).mp
  rw [Real.log_mul (by positivity) (positiveR j).ne',Real.log_pow,
    Real.log_mul (Real.exp_pos _).ne' (positiveR _).ne',Real.log_exp]
  dsimp [deficit] at good
  push_cast at good
  linarith

end Erdos142ScaleWindows

namespace Erdos142PhaseWeights
open Erdos142ScaleWindows Finset

/-- On a regular dyadic window, every actual output satisfies the uniform phase
bound. The displayed input period q need not divide either dyadic endpoint. -/
theorem regular_window_output {j M q p : ℕ} (qp : 0 < q) (pp : 0 < p)
    {δ : ℝ} (good : deficit (j+M)-deficit j ≤ δ)
    (A : Finset ℕ) (bound : A ⊆ range (2^(j+M))) (free : ThreeAPFree (A:Set ℕ))
    (D : Finset (ZMod p)) (f : ZMod p → ℤ) (shift : ℤ) (O : Finset ℤ)
    (out : ∀ u ∈ O, (u:ZMod p) ∈ D ∧ ∃ a ∈ A, f (u:ZMod p)+(u/(p:ℤ))*q=(a:ℤ)+shift) :
    (q:ℝ)*O.card ≤ D.card*(1+q/(2:ℝ)^M)*Real.exp δ*rothNumberNat (2^(j+M)) := by
  have up : (q:ℝ)*O.card ≤ D.card*((2:ℝ)^M+q)*rothNumberNat (2^j) := by
    exact_mod_cast rounded_window qp pp A bound free D f shift O out
  have reg:=regular_ratio good
  calc _ ≤ _ := up
       _ = D.card*(1+q/(2:ℝ)^M)*((2:ℝ)^M*rothNumberNat (2^j)) := by field_simp
       _ ≤ D.card*(1+q/(2:ℝ)^M)*(Real.exp δ*rothNumberNat (2^(j+M))) :=
         mul_le_mul_of_nonneg_left reg (by positivity)
       _ = _ := by ring

/-- The same regular dyadic window controls every intermediate length. -/
theorem regular_interval_output {j M q p N : ℕ} (qp : 0 < q) (pp : 0 < p)
    (within : N ≤ 2^(j+M)) {δ : ℝ} (good : deficit (j+M)-deficit j ≤ δ)
    (A : Finset ℕ) (bound : A ⊆ range N) (free : ThreeAPFree (A:Set ℕ))
    (D : Finset (ZMod p)) (f : ZMod p → ℤ) (shift : ℤ) (O : Finset ℤ)
    (out : ∀ u ∈ O, (u:ZMod p) ∈ D ∧ ∃ a ∈ A, f (u:ZMod p)+(u/(p:ℤ))*q=(a:ℤ)+shift) :
    ((N:ℝ)-(2:ℝ)^j-(1-Real.exp (-δ))*(2:ℝ)^(j+M))*q*O.card ≤
      D.card*(N+q*(2:ℝ)^j)*rothNumberNat N := by
  have scale : (2:ℕ)^(j+M)=2^M*2^j := by rw [pow_add,Nat.mul_comm]
  have reg:=regular_ratio good
  have retained : Real.exp (-δ)*(2:ℝ)^M*rothNumberNat (2^j) ≤ rothNumberNat (2^(j+M)) := by
    calc _ = Real.exp (-δ)*((2:ℝ)^M*rothNumberNat (2^j)) := by ring
         _ ≤ Real.exp (-δ)*(Real.exp δ*rothNumberNat (2^(j+M))) :=
           mul_le_mul_of_nonneg_left reg (Real.exp_pos _).le
         _ = _ := by rw [←mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
  rw [scale] at within retained
  have h:=intermediate_bound (K:=2^M) (L:=2^j) (pow_pos (by decide) _) qp pp within
    (by exact_mod_cast retained) A bound free D f shift O out
  rw [show (2:ℝ)^(j+M)=(2:ℝ)^M*2^j by rw [pow_add,mul_comm]]
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using h

end Erdos142PhaseWeights

namespace Erdos142PhaseWeights
open Finset

/-- A finite collection of locally chosen periodic rules, with arbitrary shifts
and output overlaps, is controlled by the sum of its input periods. -/
theorem blockwise_output {ι : Type*} (I : Finset ι) {L N : ℕ} (lp : 0 < L)
    (q p n : ι → ℕ) (qp : ∀ i∈I, 0 < q i) (pp : ∀ i∈I, 0 < p i)
    (A : ι → Finset ℕ) (bound : ∀ i∈I, A i ⊆ range (n i))
    (free : ∀ i∈I, ThreeAPFree (A i:Set ℕ))
    (D : (i:ι) → Finset (ZMod (p i))) (f : (i:ι) → ZMod (p i) → ℤ)
    (shift : ι → ℤ) (O : ι → Finset ℤ)
    (out : ∀ i∈I, ∀ u∈O i, (u:ZMod (p i))∈D i ∧
      ∃ a∈A i, f i (u:ZMod (p i))+(u/(p i:ℤ))*(q i)=(a:ℤ)+shift i)
    (lengths : ∑ i∈I, n i ≤ N) {ρ : ℝ} (nonneg : 0 ≤ ρ)
    (mass : ∀ i∈I, ((D i).card:ℝ) ≤ ρ*q i) :
    (L:ℝ)*(I.biUnion O).card ≤ ρ*(N+(L:ℝ)*(∑ i∈I, q i))*rothNumberNat L := by
  classical
  have one (i:ι) (hi:i∈I) :
      (L:ℝ)*(O i).card ≤ ρ*(n i+(q i:ℝ)*L)*rothNumberNat L := by
    have cap : (L:ℝ)*q i*(O i).card ≤ (D i).card*(n i+q i*L:ℝ)*rothNumberNat L := by
      exact_mod_cast rounded_interval lp (qp i hi) (pp i hi) (A i) (bound i hi)
        (free i hi) (D i) (f i) (shift i) (O i) (out i hi)
    apply (mul_le_mul_iff_right₀ (show 0<(q i:ℝ) by exact_mod_cast qp i hi)).mp
    calc _ = (L:ℝ)*q i*(O i).card := by ring
         _ ≤ _ := cap
         _ ≤ (ρ*q i)*(n i+q i*L:ℝ)*rothNumberNat L := by
           gcongr
           exact mass i hi
         _ = _ := by ring
  have union_le : ((I.biUnion O).card:ℝ) ≤ ∑ i∈I, ((O i).card:ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s:=I) (t:=O))
  have tot : (∑ i∈I, (n i:ℝ)) ≤ N := by exact_mod_cast lengths
  calc
    _ ≤ (L:ℝ)*(∑ i∈I, ((O i).card:ℝ)) := mul_le_mul_of_nonneg_left union_le (Nat.cast_nonneg _)
    _ = ∑ i∈I, (L:ℝ)*(O i).card := Finset.mul_sum _ _ _
    _ ≤ ∑ i∈I, ρ*(n i+q i*L:ℝ)*rothNumberNat L := Finset.sum_le_sum one
    _ = ρ*((∑ i∈I, (n i:ℝ))+(L:ℝ)*(∑ i∈I, q i))*rothNumberNat L := by
      rw [←Finset.sum_mul,←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_mul]
      push_cast
      ring
    _ ≤ _ := by gcongr

end Erdos142PhaseWeights

#print axioms Erdos142PhaseWeights.actual_output_le_pairs
#print axioms Erdos142PhaseWeights.phase_sum
#print axioms Erdos142PhaseWeights.realize_phase
#print axioms Erdos142PhaseWeights.rounded_interval
#print axioms Erdos142ScaleWindows.window_count
#print axioms Erdos142ScaleWindows.regular_ratio
#print axioms Erdos142PhaseWeights.regular_window_output
#print axioms Erdos142PhaseWeights.regular_interval_output
#print axioms Erdos142PhaseWeights.blockwise_output
