import Mathlib

/-! # The exact density of universal periodic substitutions through dilation four

Credit: @Deldor14. The basic height, its calibration, the cyclic maximum
obstruction, and the implication from universal preservation are repeated from
the companion PeriodicSubstitution.lean to make this file standalone.
-/

namespace Erdos142PeriodicDyadic
open Finset

/-- The discrepancy between the label and the linear slope, in lowest terms. -/
def height {p : ℕ} (P Q : ℕ) (label : ZMod p → ℤ) (r : ZMod p) : ℤ :=
  (P:ℤ)*label r-(Q:ℤ)*r.val

private theorem equal_remainder {p P Q : ℕ} (cop : Q.Coprime P) (label : ZMod p → ℤ)
    {r s : ZMod p} (eq : height P Q label r = height P Q label s) : r.val%P=s.val%P := by
  have cast := congrArg (fun a : ℤ => (a : ZMod P)) eq
  simp only [height,Int.cast_sub,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,
    zero_mul,zero_sub,neg_inj] at cast
  have unit := (ZMod.isUnit_iff_coprime Q P).mpr cop
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp (unit.mul_left_cancel cast)

/-- The finite obstruction. The output and input periods are `g*P` and `g*Q`,
where `P` and `Q` are coprime. Midpoint preservation is required for all
cyclic progressions, including repeated residues. -/
theorem mask_bound {g P Q : ℕ} (gp : 0 < g) (pos : 0 < P) (cop : Q.Coprime P)
    (D : Finset (ZMod (g*P))) (label : ZMod (g*P) → ℤ)
    (mid : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, x+z=2*y →
      height P Q label x+height P Q label z=2*height P Q label y) :
    2*D.card ≤ g*P+g := by
  have : NeZero (g*P) := ⟨(Nat.mul_pos gp pos).ne'⟩
  classical
  by_cases empty : D=∅
  · simp [empty]
  obtain ⟨y,hy,highest⟩ := D.exists_max_image (height P Q label) (Finset.nonempty_iff_ne_empty.mpr empty)
  let ref := fun x : ZMod (g*P) => 2*y-x
  have inj : Function.Injective ref := by intro u v e; dsimp [ref] at e; exact sub_right_inj.mp e
  let I := D ∩ D.image ref
  have level {x} (mem : x∈I) : height P Q label x=height P Q label y := by
    obtain ⟨xd,ri⟩ := Finset.mem_inter.mp mem
    obtain ⟨s,sd,rfl⟩ := Finset.mem_image.mp ri
    have ap : s+ref s=2*y := by dsimp [ref]; abel
    have eq := mid s sd y hy (ref s) xd ap
    have e₁ := highest s sd
    have e₂ := highest (ref s) xd
    omega
  have fit : ∀ x ∈ I, x.val/P ∈ range g := by
    intro x _
    exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul pos).mpr x.val_lt)
  have inc : (I:Set (ZMod (g*P))).InjOn (fun x => x.val/P) := by
    intro x hx z hz eq
    have rema := equal_remainder cop label ((level hx).trans (level hz).symm)
    have xx := Nat.div_add_mod x.val P
    have zz := Nat.div_add_mod z.val P
    change x.val/P=z.val/P at eq
    rw [eq,rema] at xx
    exact ZMod.val_injective _ (by omega)
  have bound := Finset.card_le_card_of_injOn (s:=I) (t:=range g) (fun x => x.val/P) fit inc
  rw [Finset.card_range] at bound
  have total := Finset.card_union_add_card_inter D (D.image ref)
  rw [Finset.card_image_of_injective _ inj] at total
  have size := Finset.card_le_univ (D ∪ D.image ref)
  rw [ZMod.card] at size
  change (D ∪ D.image ref).card+I.card=_ at total
  omega

theorem no_gain {g P Q : ℕ} (gp : 0 < g) (pos : 0 < P) (cop : Q.Coprime P)
    (small : P < 2*Q) (D : Finset (ZMod (g*P))) (label : ZMod (g*P) → ℤ)
    (mid : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, x+z=2*y →
      height P Q label x+height P Q label z=2*height P Q label y) : D.card ≤ g*Q := by
  have b := mask_bound gp pos cop D label mid
  have h := Nat.mul_le_mul_left g (show P+1 ≤ 2*Q by omega)
  rw [Nat.mul_add,Nat.mul_one,show g*(2*Q)=2*(g*Q) by ring] at h
  omega

def Free3 (S : Set ℤ) :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a < b → b < c → a+c ≠ 2*b

/-- Lift labels from a fundamental period using Euclidean division. -/
def lifted {g P : ℕ} (Q : ℕ) (label : ZMod (g*P) → ℤ) (t : ℤ) : ℤ :=
  label (t:ZMod (g*P)) + (t / ((g*P:ℕ):ℤ))*(g*Q:ℕ)

private theorem calibration {g P Q : ℕ} (gp : 0 < g) (pp : 0 < P)
    (label : ZMod (g*P) → ℤ) (t : ℤ) :
    (P:ℤ)*lifted Q label t = (Q:ℤ)*t + height P Q label (t:ZMod (g*P)) := by
  have : NeZero (g*P) := ⟨(Nat.mul_pos gp pp).ne'⟩
  rw [lifted,height,ZMod.val_intCast]
  have e := Int.emod_add_ediv_mul t ((g*P:ℕ):ℤ)
  push_cast at e ⊢
  linear_combination (Q:ℤ)*e

private theorem free_of_three {a b c : ℤ} (lt : a < b) (lt' : b < c) (bad : a+c≠2*b) :
    Free3 ({a,b,c}:Set ℤ) := by
  intro s hs t ht u hu st tu
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hs ht hu
  rcases hs with rfl|rfl|rfl <;> rcases ht with rfl|rfl|rfl <;> rcases hu with rfl|rfl|rfl <;> omega

/-- Preservation is required only for finite inputs. -/
def Universal {g P : ℕ} (Q : ℕ) (D : Finset (ZMod (g*P))) (label : ZMod (g*P) → ℤ) :=
  ∀ S : Finset ℤ, Free3 (S:Set ℤ) → Free3 {t | (t:ZMod (g*P)) ∈ D ∧ lifted Q label t ∈ S}

theorem universal_midpoint {g P Q : ℕ} (gp : 0 < g) (pp : 0 < P) (qp : 0 < Q)
    (D : Finset (ZMod (g*P))) (label : ZMod (g*P) → ℤ) (U : Universal Q D label)
    {x y z : ZMod (g*P)} (xd : x∈D) (yd : y∈D) (zd : z∈D) (mid : x+z=2*y) :
    height P Q label x+height P Q label z=2*height P Q label y := by
  let p := g*P
  have ppos : 0 < p := Nat.mul_pos gp pp
  have : NeZero (g*P) := ⟨ppos.ne'⟩
  let H := height P Q label
  let T := (H x-H y).natAbs+(H y-H z).natAbs+1
  let d := (y-x).val + p*T
  have large : T ≤ d := by
    dsimp [d]; exact le_trans (Nat.le_mul_of_pos_left _ ppos) (by omega)
  have qlarge : (d:ℤ) ≤ (Q:ℤ)*d := by exact_mod_cast Nat.le_mul_of_pos_left d qp
  have castlarge : (T:ℤ) ≤ d := by exact_mod_cast large
  dsimp [T] at castlarge
  push_cast at castlarge
  have i₁ := le_abs_self (H x-H y)
  have i₂ := le_abs_self (H y-H z)
  have a₁ := abs_nonneg (H x-H y)
  have a₂ := abs_nonneg (H y-H z)
  have dpos : (0:ℤ) < d := by omega
  have dmod : (d : ZMod (g*P))=y-x := by simp [d,p]
  let b : ℤ := y.val
  let a : ℤ := b-d
  let c : ℤ := b+d
  have bb : (b:ZMod (g*P))=y := by simp [b]
  have aa : (a:ZMod (g*P))=x := by simp [a,bb,dmod]
  have cc : (c:ZMod (g*P))=z := by
    simp only [c,Int.cast_add,Int.cast_natCast,bb,dmod]
    linear_combination -mid
  let F := lifted Q label
  have ea : (P:ℤ)*F a=Q*a+H x := (calibration gp pp label a).trans (by rw [aa])
  have eb : (P:ℤ)*F b=Q*b+H y := (calibration gp pp label b).trans (by rw [bb])
  have ec : (P:ℤ)*F c=Q*c+H z := (calibration gp pp label c).trans (by rw [cc])
  have Ppos : (0:ℤ) < P := by exact_mod_cast pp
  have ab : F a < F b := by
    apply (mul_lt_mul_iff_right₀ Ppos).mp
    rw [ea,eb]; dsimp [a]; rw [mul_sub]; omega
  have bc : F b < F c := by
    apply (mul_lt_mul_iff_right₀ Ppos).mp
    rw [eb,ec]; dsimp [c]; rw [mul_add]; omega
  have integral : a+c=2*b := by dsimp [a,c]; omega
  have labels : F a+F c=2*F b := by
    by_contra different
    let S : Finset ℤ := {F a,F b,F c}
    have hs : Free3 (S:Set ℤ) := by simpa [S] using free_of_three ab bc different
    have valid := U S hs
    have ma : (a:ZMod (g*P)) ∈ D ∧ F a ∈ S := ⟨aa ▸ xd, by simp [S]⟩
    have mb : (b:ZMod (g*P)) ∈ D ∧ F b ∈ S := ⟨bb ▸ yd, by simp [S]⟩
    have mc : (c:ZMod (g*P)) ∈ D ∧ F c ∈ S := ⟨cc ▸ zd, by simp [S]⟩
    exact valid a ma b mb c mc (by dsimp [a]; omega) (by dsimp [c]; omega) integral
  change H x+H z=2*H y
  linear_combination -ea-ec+2*eb+(P:ℤ)*labels-(Q:ℤ)*integral

theorem universal_no_gain {g P Q : ℕ} (gp : 0 < g) (pp : 0 < P) (qp : 0 < Q)
    (cop : Q.Coprime P) (small : P < 2*Q) (D : Finset (ZMod (g*P)))
    (label : ZMod (g*P) → ℤ) (U : Universal Q D label) : D.card ≤ g*Q :=
  no_gain gp pp cop small D label (fun _ hx _ hy _ hz ap => universal_midpoint gp pp qp D label U hx hy hz ap)

private def cell (A : Finset ℕ) (n s r : ℕ) : Finset ℕ :=
  (range n).filter (fun t => s*t+r∈A)

private theorem majority_cell (A : Finset ℕ) {n s : ℕ} (sp : 0<s)
    (bounds : A ⊆ range (s*n)) (big : s*n < 2*A.card) :
    ∃ r < s, n < 2*(cell A n s r).card := by
  classical
  let B := fun r => (cell A n s r).image (fun t => s*t+r)
  have cover : A ⊆ (range s).biUnion B := by
    intro t ht
    apply mem_biUnion.mpr
    refine ⟨t%s,mem_range.mpr (Nat.mod_lt _ sp),mem_image.mpr ⟨t/s,?_,?_⟩⟩
    · apply mem_filter.mpr
      have b:= mem_range.mp (bounds ht)
      exact ⟨mem_range.mpr ((Nat.div_lt_iff_lt_mul sp).mpr (by simpa [Nat.mul_comm] using b)),
        (Nat.div_add_mod t s).symm ▸ ht⟩
    · exact Nat.div_add_mod t s
  have top := (Finset.card_le_card cover).trans (Finset.card_biUnion_le)
  by_contra! h
  have small : ∑ r ∈ range s, 2*(B r).card ≤ ∑ _r ∈ range s, n := by
    apply Finset.sum_le_sum
    intro r hr
    exact (Nat.mul_le_mul_left 2 Finset.card_image_le).trans (h r (mem_range.mp hr))
  rw [← Finset.mul_sum] at small
  simp at small
  omega

private theorem reflected_pair {m : ℕ} (mp : 0 < m) (B : Finset ℕ) (bounds : B ⊆ range m)
    (major : m<2*B.card) (y e : ℕ) :
    ∃ i∈B, ∃ j∈B, i+j+e ≡ y [MOD m] := by
  classical
  have : NeZero m := ⟨mp.ne'⟩
  let R := fun t : ℕ => ((y:ZMod m)-e-t).val
  have val {t : ℕ} (ht : t∈B) : (t:ZMod m).val=t := by
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (mem_range.mp (bounds ht))]
  have inj : (B:Set ℕ).InjOn R := by
    intro i hi j hj h
    have cast := congrArg (fun v : ℕ => (v:ZMod m)) h
    simp [R] at cast
    simpa only [val hi,val hj] using congrArg ZMod.val cast
  have size := Finset.card_union_add_card_inter B (B.image R)
  rw [Finset.card_image_of_injOn inj] at size
  have ub := Finset.card_le_card (t:=range m) (s:=B ∪ B.image R) (by
    intro t ht
    rcases mem_union.mp ht with hb|hb
    · exact bounds hb
    · obtain ⟨i,hi,rfl⟩:=mem_image.mp hb
      exact mem_range.mpr (ZMod.val_lt _))
  rw [card_range] at ub
  obtain ⟨j,ji⟩ := Finset.card_pos.mp (show 0<(B ∩ B.image R).card by omega)
  obtain ⟨jb,jr⟩ := mem_inter.mp ji
  obtain ⟨i,ib,rfl⟩ := mem_image.mp jr
  refine ⟨i,ib,R i,jb,(ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
  push_cast
  simp [R]

/-- On a cyclic group of order a power of two, any midpoint-preserving integer
height on a strict majority of the group is constant. Representatives are naturals. -/
theorem dyadic_majority_height (a : ℕ) (A : Finset ℕ) (H : ℕ → ℤ)
    (bounds : A ⊆ range (2^a)) (major : 2^a < 2*A.card)
    (mid : ∀ i ∈ A, ∀ j ∈ A, ∀ k ∈ A, i+k ≡ 2*j [MOD 2^a] → H i+H k=2*H j) :
    ∃ c : ℤ, ∀ i ∈ A, H i=c := by
  classical
  induction a generalizing A H with
  | zero =>
    refine ⟨H 0,fun i hi => ?_⟩
    have := mem_range.mp (bounds hi)
    simp at this
    rw [this]
  | succ a ih =>
    let m := 2^a
    have mp : 0 < m := pow_pos (by decide) _
    have mn : 2^(a+1)=2*m := by rw [pow_succ,Nat.mul_comm]
    rw [mn] at bounds major mid
    obtain ⟨e,es,hm⟩ := majority_cell A (by decide : 0<2) bounds major
    let B := cell A m 2 e
    have bb : B ⊆ range m := fun _ h => (mem_filter.mp h).1
    have em {i} (h : i∈B) : 2*i+e∈A := (mem_filter.mp h).2
    obtain ⟨c,hc⟩ := ih B (fun i => H (2*i+e)) bb hm (by
      intro i hi j hj k hk h
      apply mid _ (em hi) _ (em hj) _ (em hk)
      have big : 2*(i+k) ≡ 2*(2*j) [MOD 2*m] := h.mul_left' 2
      convert big.add_right (e+e) using 1 <;> ring)
    refine ⟨c,fun y hy => ?_⟩
    obtain ⟨i,hi,k,hk,h⟩ := reflected_pair mp B bb hm y e
    have scale : 2*(i+k+e) ≡ 2*y [MOD 2*m] := h.mul_left' 2
    have h₁ := mid _ (em hi) _ hy _ (em hk) (by convert scale using 1; ring)
    have h₂:=hc i hi
    have h₃:=hc k hk
    omega


/-- On a cyclic group of even order, an integer height that determines the parity
of its argument and preserves all occupied midpoints forces density at most one half. -/
theorem parity_height_bound (n : ℕ) (pos : 0 < n) (ev : 2 ∣ n)
    (A : Finset ℕ) (H : ℕ → ℤ) (bounds : A ⊆ range n)
    (mid : ∀ i ∈ A, ∀ j ∈ A, ∀ k ∈ A, i+k ≡ 2*j [MOD n] → H i+H k=2*H j)
    (par : ∀ i ∈ A, ∀ k ∈ A, H i=H k → i ≡ k [MOD 2]) : 2*A.card ≤ n := by
  classical
  by_contra! big
  obtain ⟨a,s,odd,fac⟩ := Nat.exists_eq_two_pow_mul_odd pos.ne'
  have sp := odd.pos
  have dim : n=s*2^a := by simpa [Nat.mul_comm] using fac
  have d2 : 2 ∣ 2^a := by
    cases a with
    | zero => simp at fac; rw [fac] at ev; exact False.elim (odd.not_two_dvd_nat ev)
    | succ a => exact ⟨2^a,by rw [pow_succ,Nat.mul_comm]⟩
  obtain ⟨r,rs,large⟩ := majority_cell A sp (dim ▸ bounds) (dim ▸ big)
  let B:=cell A (2^a) s r
  have bb : B ⊆ range (2^a) := fun _ h => (mem_filter.mp h).1
  have em {i} (hi : i∈B) : s*i+r∈A := (mem_filter.mp hi).2
  obtain ⟨c,hc⟩ := dyadic_majority_height a B (fun i => H (s*i+r)) bb large (by
    intro i hi j hj k hk h
    apply mid _ (em hi) _ (em hj) _ (em hk)
    rw [dim]
    have scaled := h.mul_left' s
    convert scaled.add_right (r+r) using 1 <;> ring)
  obtain ⟨i,hi,j,hj,sum⟩ := reflected_pair (pow_pos (by decide) _) B bb large 1 0
  have eq := par _ (em hi) _ (em hj) ((hc i hi).trans (hc j hj).symm)
  have dsum := sum.of_dvd d2
  change (s*i+r)%2=(s*j+r)%2 at eq
  change (i+j+0)%2=1%2 at dsum
  have so : s%2=1 := Nat.odd_iff.mp odd
  simp only [Nat.add_mod _ r,Nat.mul_mod s,so,one_mul,Nat.mod_mod] at eq
  omega

/-- This improves the obstruction by half a fiber when the reduced numerator is even. -/
theorem even_mask_bound {g P Q : ℕ} (gp : 0<g) (pp : 0<P) (cop : Q.Coprime P)
    (ev : 2 ∣ P) (D : Finset (ZMod (g*P))) (label : ZMod (g*P) → ℤ)
    (mid : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, x+z=2*y →
      height P Q label x+height P Q label z=2*height P Q label y) : 2*D.card≤g*P := by
  classical
  have pn := Nat.mul_pos gp pp
  have : NeZero (g*P) := ⟨pn.ne'⟩
  let A := D.image ZMod.val
  have rep {i} (hi : i∈A) : (i:ZMod (g*P))∈D ∧ (i:ZMod (g*P)).val=i := by
    obtain ⟨r,hr,rfl⟩:=mem_image.mp hi
    simp [hr]
  have bounds : A ⊆ range (g*P) := by
    intro t ht
    rw [← (rep ht).2]
    exact mem_range.mpr (ZMod.val_lt _)
  have ans := parity_height_bound (g*P) pn (ev.trans (dvd_mul_left _ _))
    A (fun i => height P Q label (i:ZMod (g*P))) bounds (by
      intro i hi j hj k hk h
      apply mid _ (rep hi).1 _ (rep hj).1 _ (rep hk).1
      have cast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
      push_cast at cast
      exact cast) (by
      intro i hi k hk h
      have cast := congrArg (fun z : ℤ => (z:ZMod P)) h
      simp only [height,Int.cast_sub,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,
        zero_mul,zero_sub,neg_inj,(rep hi).2,(rep hk).2] at cast
      have unit := (ZMod.isUnit_iff_coprime Q P).mpr cop
      exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp (unit.mul_left_cancel cast)).of_dvd ev)
  rwa [show A.card=D.card from Finset.card_image_of_injective _ (ZMod.val_injective _)] at ans

theorem universal_no_gain_closed {g P Q : ℕ} (gp : 0<g) (pp : 0<P) (qp : 0<Q)
    (cop : Q.Coprime P) (small : P≤2*Q) (D : Finset (ZMod (g*P)))
    (label : ZMod (g*P) → ℤ) (U : Universal Q D label) : D.card≤g*Q := by
  rcases small.lt_or_eq with h|h
  · exact universal_no_gain gp pp qp cop h D label U
  · have ans := even_mask_bound gp pp cop (show 2 ∣ P from ⟨Q,h⟩) D label
      (fun _ hx _ hy _ hz ap => universal_midpoint gp pp qp D label U hx hy hz ap)
    have scale : g*P=2*(g*Q) := by rw [h]; ring
    omega

/-- Consecutive digits prevent cyclic carries when their doubled width is below the
output period. The second width condition rules out a constant input progression. -/
theorem interval_substitution_free {P q w : ℤ} (qp : 0 < q) (wp : 0  ≤  w)
    (wrap : 2*w < P) (width : w < 2*q) (S : Set ℤ) (hs : Free3 S) :
    Free3 {x | ∃ k r : ℤ, 0 ≤ r ∧ r ≤ w ∧ x=P*k+r ∧ q*k+r ∈ S} := by
  intro a ha b hb c hc ab bc eq
  obtain ⟨i,r,rl,ru,ri,ar⟩:=ha
  obtain ⟨j,s,sl,su,sj,bs⟩:=hb
  obtain ⟨k,t,tl,tu,tk,ct⟩:=hc
  have pp : 0 < P := by omega
  have zero : P*(i+k-2*j)=2*s-r-t := by
    rw [ri,sj,tk] at eq; linear_combination eq
  have prog : i+k=2*j := by
    rcases lt_trichotomy (i+k) (2*j) with h|h|h
    · have ineq := mul_le_mul_of_nonneg_left (show i+k-2*j ≤  -1 by omega) pp.le
      rw [zero,mul_neg_one] at ineq
      omega
    · exact h
    · have ineq := mul_le_mul_of_nonneg_left (show 1 ≤ i+k-2*j by omega) pp.le
      rw [zero,mul_one] at ineq
      omega
  have digits : r+t=2*s := by rw [show i+k-2*j=0 by omega,mul_zero] at zero; omega
  have ij : i ≤ j := by
    by_contra! neg
    have hi := mul_le_mul_of_nonneg_left (show j+1 ≤ i by omega) pp.le
    rw [ri,sj] at ab
    nlinarith only [hi,ab,rl,su,wrap,wp]
  have strict : q*i+r < q*j+s := by
    rcases ij.eq_or_lt with h|h
    · subst j; rw [ri,sj] at ab; omega
    · have hi := mul_le_mul_of_nonneg_left (show i+1 ≤ j by omega) qp.le
      rw [mul_add,mul_one] at hi
      omega
  have labelAP : (q*i+r)+(q*k+t)=2*(q*j+s) := by
    linear_combination q*prog+digits
  exact hs _ ar _ bs _ ct strict (by omega) labelAP

/-- The first L consecutive residues in each of g primitive periods. -/
def intervalMask (g P L : ℕ) : Finset (ZMod (g*P)) :=
  ((range g) ×ˢ (range L)).image (fun t : ℕ×ℕ => ((t.1*P+t.2:ℕ):ZMod (g*P)))

/-- Repeat the same primitive substitution g times in the displayed period. -/
def intervalLabel {g P : ℕ} (Q : ℕ) (x : ZMod (g*P)) : ℤ :=
  (Q:ℤ)*(x.val/P:ℕ)+(x.val%P:ℕ)

private theorem tag_bounds {g P L : ℕ} (lp : L ≤ P) (t : ℕ×ℕ)
    (ht : t ∈ (range g) ×ˢ (range L)) : t.1*P+t.2 < g*P ∧ t.2<P := by
  obtain ⟨hi,hj⟩:=Finset.mem_product.mp ht
  have i:=Finset.mem_range.mp hi
  have j:=Finset.mem_range.mp hj
  have h:=Nat.mul_le_mul_right P (show t.1+1 ≤ g by omega)
  rw [Nat.add_mul,Nat.one_mul] at h
  omega

private theorem tag_div {P r : ℕ} (k : ℕ) (pp : 0 < P) (rp : r < P) :
    (k*P+r)/P=k := by rw [Nat.mul_comm k P,Nat.mul_add_div pp,Nat.div_eq_of_lt rp,Nat.add_zero]

theorem intervalMask_card {g P L : ℕ} (lp : L ≤ P) :
    (intervalMask g P L).card=g*L := by
  classical
  rw [intervalMask,Finset.card_image_of_injOn,Finset.card_product,Finset.card_range,Finset.card_range]
  intro i hi j hj h
  obtain ⟨bi,ui⟩:=tag_bounds lp i hi
  obtain ⟨bj,uj⟩:=tag_bounds lp j hj
  have eq:=congrArg ZMod.val h
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt bi,Nat.mod_eq_of_lt bj] at eq
  have pp : 0 < P := by omega
  have counts:=congrArg (fun x => x/P) eq
  simp only [tag_div i.1 pp ui,tag_div j.1 pp uj] at counts
  have digits:=congrArg (fun x => x%P) eq
  simp only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt ui,Nat.mod_eq_of_lt uj] at digits
  exact Prod.ext counts digits

theorem intervalMask_universal {g P Q L : ℕ} (gp : 0 < g) (pp : 0 < P) (qp : 0 < Q)
    (lp : L ≤ P) (wrap : 2*(L-1)<P) (width : L-1<2*Q) :
    Universal Q (intervalMask g P L) (intervalLabel Q) := by
  intro S hs
  have pn:=Nat.mul_pos gp pp
  have : NeZero (g*P) := ⟨pn.ne'⟩
  have fits (x : ℤ) (hx : (x:ZMod (g*P)) ∈ intervalMask g P L ∧
      lifted (g:=g) (P:=P) Q (intervalLabel Q) x ∈ S) :
      ∃ k r : ℤ, 0 ≤ r ∧ r ≤ ((L-1:ℕ):ℤ) ∧ x=(P:ℤ)*k+r ∧ (Q:ℤ)*k+r∈S := by
    obtain ⟨v,hv,he⟩:=Finset.mem_image.mp hx.1
    obtain ⟨small,digit⟩:=tag_bounds lp v hv
    have vl:=Finset.mem_range.mp (Finset.mem_product.mp hv).2
    have val : (x:ZMod (g*P)).val=v.1*P+v.2 := by
      rw [←he,ZMod.val_natCast,Nat.mod_eq_of_lt small]
    let t:=x/((g*P:ℕ):ℤ)
    refine ⟨t*g+v.1,v.2,by positivity,by exact_mod_cast (show v.2 ≤ L-1 by omega),?_,?_⟩
    · have div:=Int.emod_add_ediv_mul x ((g*P:ℕ):ℤ)
      have rep : x%((g*P:ℕ):ℤ)=((v.1*P+v.2:ℕ):ℤ) := by
        rw [←val,ZMod.val_intCast]
      rw [rep] at div
      dsimp [t]
      push_cast at div ⊢
      linarith only [div]
    · have mem:=hx.2
      simp only [lifted,intervalLabel,val,tag_div v.1 pp digit,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt digit] at mem
      convert mem using 1
      dsimp [t]
      ring
  intro a ha b hb c hc ab bc ap
  apply interval_substitution_free (by exact_mod_cast qp) (by positivity)
    (by exact_mod_cast wrap) (by exact_mod_cast width) (S:Set ℤ) hs a (fits a ha) b (fits b hb) c
    (fits c hc) ab bc ap

/-- The exact optimal number of occupied positions, allowing any common period
multiple g. For dilations through four consecutive digits attain the upper bound. -/
theorem optimal_universal_mask {g P Q : ℕ} (gp : 0 < g) (pp : 0 < P) (qp : 0 < Q)
    (cop : Q.Coprime P) (scale : P ≤ 4*Q) :
    (∀ (D : Finset (ZMod (g*P))) (label : ZMod (g*P) → ℤ),
      Universal Q D label → D.card ≤ g*((P+1)/2)) ∧
    (∃ (D : Finset (ZMod (g*P))) (label : ZMod (g*P) → ℤ),
      Universal Q D label ∧ D.card=g*((P+1)/2)) := by
  constructor
  · intro D label U
    have mid : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, x+z=2*y →
        height P Q label x+height P Q label z=2*height P Q label y :=
      fun _ hx _ hy _ hz ap => universal_midpoint gp pp qp D label U hx hy hz ap
    rcases Nat.mod_two_eq_zero_or_one P with h|h
    · have b:=even_mask_bound gp pp cop (Nat.dvd_of_mod_eq_zero h) D label mid
      have rounded : 2*((P+1)/2)=P := by omega
      have factor : 2*(g*((P+1)/2))=g*P := by
        calc _ = g*(2*((P+1)/2)) := by ring
             _ = _ := by rw [rounded]
      omega
    · have b:=mask_bound gp pp cop D label mid
      have rounded : 2*((P+1)/2)=P+1 := by omega
      have factor : 2*(g*((P+1)/2))=g*P+g := by
        calc _ = g*(2*((P+1)/2)) := by ring
             _ = _ := by rw [rounded];ring
      omega
  · let L:=(P+1)/2
    have lp : L ≤ P := by dsimp [L]; omega
    refine ⟨intervalMask g P L,intervalLabel Q,intervalMask_universal gp pp qp lp ?_ ?_,intervalMask_card lp⟩
    all_goals dsimp [L]; omega

/-- The only exceptions to a loss of at least one seventh below dilation 13/8
are the identity and dilation 3/2. The ratio 11/7 attains the cutoff. -/
theorem below_thirteen_eighths {g P Q : ℕ} (gp : 0 < g) (pp : 0 < P) (qp : 0 < Q)
    (cop : Q.Coprime P) (scale : 8*P<13*Q)
    (except1 : P≠1 ∨ Q≠1) (except2 : P≠3 ∨ Q≠2)
    (D : Finset (ZMod (g*P))) (label : ZMod (g*P) → ℤ) (U : Universal Q D label) :
    7*D.card ≤ 6*(g*Q) := by
  have cardinal := (optimal_universal_mask gp pp qp cop (by omega)).1 D label U
  have ratio : 7*((P+1)/2) ≤ 6*Q := by
    by_contra! bad
    have small : Q ≤ 11 := by omega
    interval_cases Q <;> omega
  calc 7*D.card ≤ 7*(g*((P+1)/2)) := Nat.mul_le_mul_left _ cardinal
       _ = g*(7*((P+1)/2)) := by ring
       _ ≤ g*(6*Q) := Nat.mul_le_mul_left g ratio
       _ = _ := by ring

end Erdos142PeriodicDyadic
#print axioms Erdos142PeriodicDyadic.dyadic_majority_height
#print axioms Erdos142PeriodicDyadic.parity_height_bound
#print axioms Erdos142PeriodicDyadic.even_mask_bound
#print axioms Erdos142PeriodicDyadic.universal_no_gain_closed
#print axioms Erdos142PeriodicDyadic.intervalMask_card
#print axioms Erdos142PeriodicDyadic.intervalMask_universal
#print axioms Erdos142PeriodicDyadic.optimal_universal_mask
#print axioms Erdos142PeriodicDyadic.below_thirteen_eighths
