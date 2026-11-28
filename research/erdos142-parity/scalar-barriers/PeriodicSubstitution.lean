import Mathlib

/-! # A finite obstruction to universal periodic substitutions for three-term progressions

A cyclic midpoint-preserving integer height is constant on every symmetric pair
through a maximum. The resulting density bound applies with nonprimitive periods.
Credit: @Deldor14.
-/

namespace Erdos142PeriodicSubstitution
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

private theorem pieces (F : ℕ → ℕ) (zero : F 0=0) (sub : ∀ a b, F (a+b) ≤ F a+F b)
    (j m : ℕ) : F (j*m) ≤ j*F m := by
  induction j with
  | zero => simp [zero]
  | succ j ih =>
    rw [Nat.succ_mul,Nat.succ_mul]
    exact (sub (j*m) m).trans (Nat.add_le_add_right ih _)

/-- The gap bound for three terms is a consequence of older interval inequalities,
including the exact one-site saving in gluing. -/
theorem gap_redundant (F : ℕ → ℕ) (zero : F 0=0) (mono : Monotone F)
    (sub : ∀ a b, F (a+b) ≤ F a+F b)
    (glue : ∀ a b, 0 < b → b ≤ a → F a+F b ≤ F (2*a+b-1))
    (m n : ℕ) (mp : 0 < m) : m*F n ≤ (n+(m-1)/2)*F m := by
  let h := (m-1)/2
  have short (r : ℕ) (rm : r < m) : m*F r ≤ (r+h)*F m := by
    by_cases rz : r=0
    · simp [rz,zero]
    have rp : 0 < r := Nat.pos_of_ne_zero rz
    by_cases inside : m ≤ r+h
    · exact Nat.mul_le_mul inside (mono rm.le)
    have less : 2*r ≤ m := by dsimp [h] at inside; omega
    by_cases far : 3*r-1 ≤ m
    · have two := (glue r r rp le_rfl).trans (mono (show 2*r+r-1 ≤ m by omega))
      have count : m ≤ 2*(r+h) := by dsimp [h]; omega
      calc
        _ ≤ (2*(r+h))*F r := Nat.mul_le_mul_right _ count
        _ = (r+h)*(F r+F r) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ two
    let p := 2*r-1
    let x := m-p
    have xp : 0 < x := by dsimp [x,p]; omega
    have xr : x ≤ r := by dsimp [x,p]; omega
    have mx : m=p+x := by dsimp [x,p]; omega
    have joins := glue r x xp xr
    have fit : F r+F x ≤ F m := by rwa [show 2*r+x-1=m by dsimp [p] at mx; omega] at joins
    let j := (r-1)/x+1
    have rep := Nat.div_add_mod (r-1) x
    have bound := Nat.mod_lt (r-1) xp
    have lower : r ≤ j*x := by dsimp [j]; rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm _ x]; omega
    have upper : x*j ≤ p := by dsimp [j,p]; rw [Nat.mul_add,Nat.mul_one]; omega
    have covers := (mono lower).trans (pieces F zero sub j x)
    have leftover : x*F r ≤ p*F x := calc
      _ ≤ x*(j*F x) := Nat.mul_le_mul_left _ covers
      _ = (x*j)*F x := by ring
      _ ≤ p*F x := Nat.mul_le_mul_right _ upper
    have top : p ≤ r+h := by dsimp [p,h]; omega
    calc
      _ = p*F r+x*F r := by rw [mx,Nat.add_mul]
      _ ≤ p*F r+p*F x := Nat.add_le_add_left leftover _
      _ = p*(F r+F x) := by ring
      _ ≤ p*F m := Nat.mul_le_mul_left _ fit
      _ ≤ _ := Nat.mul_le_mul_right _ top
  let j := n/m
  let r := n%m
  have split : j*m+r=n := by simpa only [j,r,Nat.mul_comm j m] using Nat.div_add_mod n m
  have upper : F n ≤ j*F m+F r := by
    calc F n = F (j*m+r) := congrArg F split.symm
         _ ≤ F (j*m)+F r := sub _ _
         _ ≤ _ := Nat.add_le_add_right (pieces F zero sub j m) _
  have rest := short r (Nat.mod_lt n mp)
  calc
    _ ≤ m*(j*F m+F r) := Nat.mul_le_mul_left _ upper
    _ = (j*m)*F m+m*F r := by ring
    _ ≤ (j*m)*F m+(r+h)*F m := Nat.add_le_add_left rest _
    _ = (j*m+r+h)*F m := by ring
    _ = _ := by rw [split]

/-- Separate two arbitrary optimal sets by the shortest universal gap between
    two intervals of these lengths. Coordinates in the first interval start at zero. This lemma and its Lean proof
    are from @Deldor14’s Erdős #142 Roth-growth development. -/
private theorem roth_glue (a b n : ℕ) (hb : 0 < b) (hba : b ≤ a) (hn : 2*a+b ≤ n+1) :
    rothNumberNat a + rothNumberNat b ≤ rothNumberNat n := by
  obtain ⟨A,hA,ca,fa⟩ := rothNumberNat_spec a
  obtain ⟨B,hB,cb,fb⟩ := rothNumberNat_spec b
  let s := 2*a-1
  let lift : ℕ → ℕ := fun x => s+x
  let U := A ∪ B.image lift
  have boundA {x} (h : x ∈ A) : x < a := mem_range.mp (hA h)
  have boundB {x} (h : x ∈ B) : x < b := mem_range.mp (hB h)
  have hs : s+1=2*a := by dsimp [s]; omega
  have separate : Disjoint A (B.image lift) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hy
    have := boundA hx
    dsimp [lift] at *
    omega
  have free : ThreeAPFree (↑U : Set ℕ) := by
    apply threeAPFree_iff_eq_right.mpr
    intro x hx y hy z hz eq
    have tag {v} (h : v ∈ U) : v ∈ A ∨ ∃ t ∈ B, v=s+t := by
      rcases mem_union.mp h with h|h
      · exact Or.inl h
      · obtain ⟨t,ht,rfl⟩ := mem_image.mp h
        exact Or.inr ⟨t,ht,rfl⟩
    rcases tag hx with x0|⟨u,hu,rfl⟩ <;>
      rcases tag hy with y0|⟨v,hv,rfl⟩ <;>
      rcases tag hz with z0|⟨w,hw,rfl⟩
    all_goals try exact threeAPFree_iff_eq_right.mp fa x0 y0 z0 eq
    all_goals try
      have mid : u+w=v+v := by omega
      have uw := threeAPFree_iff_eq_right.mp fb hu hv hw mid
      omega
    all_goals
      first | have bx := boundA x0 | have bx := boundB hu
      first | have by' := boundA y0 | have by' := boundB hv
      first | have bz := boundA z0 | have bz := boundB hw
      omega
  apply free.le_rothNumberNat
  · intro x hx
    rcases mem_union.mp hx with h|h
    · have := boundA h; omega
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp h
      have := boundB hy
      dsimp [lift]; omega
  · dsimp [U]
    rw [card_union_of_disjoint separate, card_image_of_injective _ (show Function.Injective lift by
      intro x y h; dsimp [lift] at h; omega), ca, cb]


theorem roth_gap (m n : ℕ) (mp : 0 < m) :
    m*rothNumberNat n ≤ (n+(m-1)/2)*rothNumberNat m := by
  apply gap_redundant _ rothNumberNat_zero rothNumberNat.monotone rothNumberNat_add_le _ m n mp
  intro a b hb hab
  exact roth_glue a b _ hb hab (by omega)

end Erdos142PeriodicSubstitution
#print axioms Erdos142PeriodicSubstitution.mask_bound
#print axioms Erdos142PeriodicSubstitution.no_gain
#print axioms Erdos142PeriodicSubstitution.universal_no_gain
#print axioms Erdos142PeriodicSubstitution.gap_redundant
#print axioms Erdos142PeriodicSubstitution.roth_gap
