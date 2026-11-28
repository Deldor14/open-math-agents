import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic

open Finset
namespace Erdos142DyadicClusters

/-- Only genuine three-point supports are excluded. -/
def Weak (t : ℕ) (S : Finset ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
    (x+z=y+y ∨ x+z=y+y+t ∨ x+z+t=y+y ∨
     x+z=y+y+2*t ∨ x+z+2*t=y+y) → x=y ∨ y=z ∨ x=z

instance (t : ℕ) (S : Finset ℕ) : Decidable (Weak t S) := by
  unfold Weak
  infer_instance

def close (t x y : ℕ) : Prop :=
  x=y ∨ 2*x+t=2*y ∨ 2*y+t=2*x ∨ x+t=y ∨ y+t=x ∨ x+2*t=y ∨ y+2*t=x

instance (t x y : ℕ) : Decidable (close t x y) := by unfold close; infer_instance

def step (t : ℕ) (S : Finset ℕ) := S ∪ S.image (·+t)
def pairs (t : ℕ) (S : Finset ℕ) := S.filter (fun x => x+t ∈ S)

private theorem weak_mono {S T : Finset ℕ} {t : ℕ} (inc : S ⊆ T) (h : Weak t T) :
    Weak t S := fun x hx y hy z hz => h x (inc hx) y (inc hy) z (inc hz)

private theorem step_mem {t X : ℕ} {S : Finset ℕ} (h : X ∈ step t S) :
    ∃ x ∈ S, X=x ∨ X=x+t := by
  rcases mem_union.mp h with h|h
  · exact ⟨X,h,Or.inl rfl⟩
  · obtain ⟨x,hx,rfl⟩ := mem_image.mp h
    exact ⟨x,hx,Or.inr rfl⟩

/-- A progression of lifted points can only use inputs in a single connected
    component for the three possible pair distances. -/
theorem projections_close {S : Finset ℕ} {t x y z X Y Z : ℕ} (h : Weak t S)
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (a : X=x ∨ X=x+t) (b : Y=y ∨ Y=y+t) (c : Z=z ∨ Z=z+t)
    (eq : X+Z=Y+Y) : close t x y ∧ close t x z ∧ close t y z := by
  have w := h x hx y hy z hz
  unfold close
  rcases a with a|a <;> rcases b with b|b <;> rcases c with c|c <;> omega

def shapes : Finset (Finset ℕ) :=
  {{0}, {0,1}, {0,2}, {0,4}, {0,1,5}, {0,4,5}, {0,4,5,9}}

private theorem coordinates : ∀ C ∈ shapes, ∀ j ∈ C, j ≤ 9 := by decide

private theorem extension_table : ∀ C ∈ shapes, ∀ j ∈ range 14,
    (∃ i ∈ C, close 2 i j) → Weak 2 (insert j C) → insert j C ∈ shapes := by
  decide

def choices : Finset (Finset ℕ) :=
  {{0,2}, {0,1,3}, {0,2,6}, {0,1,3,7}, {0,2,5,6}, {0,2,5,6,9,11}}

private theorem choice_table : ∀ C ∈ shapes, ∃ D ∈ choices, D ⊆ step 2 C ∧
    (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, x+z=y+y → x=z) ∧
    4*C.card ≤ 3*D.card+2*(if C=({0,2}:Finset ℕ) then 1 else 0) := by decide

/-- Locate the first component in an arbitrary finite admissible set. -/
theorem first_component (S : Finset ℕ) (a : ℕ) (ha : a ∈ S)
    (lo : ∀ x ∈ S, a ≤ x) (weak : Weak 2 S) :
    ∃ C ∈ shapes, (∀ j ∈ C, a+j ∈ S) ∧
      ∀ i ∈ C, ∀ x ∈ S, close 2 (a+i) x → x-a ∈ C := by
  let pool := shapes.filter (fun C => ∀ j ∈ C, a+j ∈ S)
  have root : ({0} : Finset ℕ) ∈ pool := by
    apply mem_filter.mpr
    exact ⟨by decide,by simpa using ha⟩
  obtain ⟨C,hC,hmax⟩ := exists_max_image pool Finset.card ⟨_,root⟩
  obtain ⟨shape,inside⟩ := mem_filter.mp hC
  refine ⟨C,shape,inside,?_⟩
  intro i hi x hx adj
  let j := x-a
  have ax : a+j=x := by dsimp [j]; have := lo x hx; omega
  have small := coordinates C shape i hi
  have cl : close 2 i j := by unfold close at adj ⊢; omega
  have j14 : j ∈ range 14 := by rw [mem_range]; unfold close at cl; omega
  have valid : ∀ v ∈ insert j C, a+v ∈ S := by
    intro v hv
    rcases mem_insert.mp hv with h|h
    · simpa [h,ax] using hx
    · exact inside _ h
  have moved : Weak 2 (insert j C) := by
    intro u hu v hv w hw defect
    have h := weak _ (valid _ hu) _ (valid _ hv) _ (valid _ hw)
    omega
  have next := extension_table C shape j j14 ⟨i,hi,cl⟩ moved
  have cm := hmax (insert j C) (mem_filter.mpr ⟨next,valid⟩)
  change j ∈ C
  by_contra missing
  rw [card_insert_of_notMem missing] at cm
  omega

/-- Free choices in separated components can be made independently. -/
private theorem glue {S P Q U V : Finset ℕ} {t : ℕ} (weak : Weak t S)
    (pS : P ⊆ S) (qS : Q ⊆ S) (sep : ∀ x ∈ P, ∀ y ∈ Q, ¬close t x y)
    (uP : U ⊆ step t P) (vQ : V ⊆ step t Q)
    (fu : ThreeAPFree (↑U : Set ℕ)) (fv : ThreeAPFree (↑V : Set ℕ)) :
    ThreeAPFree (↑(U ∪ V) : Set ℕ) ∧ Disjoint U V := by
  have symm {x y} (h : close t x y) : close t y x := by unfold close at *; omega
  have tag {X} (h : X ∈ U ∪ V) :
      ∃ x ∈ S, (X=x ∨ X=x+t) ∧ ((x ∈ P ∧ X ∈ U) ∨ (x ∈ Q ∧ X ∈ V)) := by
    rcases mem_union.mp h with h|h
    · obtain ⟨x,hx,e⟩ := step_mem (uP h)
      exact ⟨x,pS hx,e,Or.inl ⟨hx,h⟩⟩
    · obtain ⟨x,hx,e⟩ := step_mem (vQ h)
      exact ⟨x,qS hx,e,Or.inr ⟨hx,h⟩⟩
  constructor
  · apply threeAPFree_iff_eq_right.mpr
    intro X hX Y hY Z hZ eq
    obtain ⟨x,hx,ex,cx⟩ := tag hX
    obtain ⟨y,hy,ey,cy⟩ := tag hY
    obtain ⟨z,hz,ez,cz⟩ := tag hZ
    obtain ⟨xy,xz,yz⟩ := projections_close weak hx hy hz ex ey ez eq
    rcases cx with ⟨xp,xu⟩|⟨xq,xv⟩ <;> rcases cy with ⟨yp,yu⟩|⟨yq,yv⟩ <;>
      rcases cz with ⟨zp,zu⟩|⟨zq,zv⟩
    all_goals first
      | exact threeAPFree_iff_eq_right.mp fu xu yu zu eq
      | exact threeAPFree_iff_eq_right.mp fv xv yv zv eq
      | exact False.elim (sep x xp y yq xy)
      | exact False.elim (sep x xp z zq xz)
      | exact False.elim (sep y yp x xq (symm xy))
      | exact False.elim (sep z zp x xq (symm xz))
  · rw [Finset.disjoint_left]
    intro X hu hv
    obtain ⟨x,hx,ex⟩ := step_mem (uP hu)
    obtain ⟨y,hy,ey⟩ := step_mem (vQ hv)
    exact sep x hx y hy (projections_close weak (pS hx) (qS hy) (qS hy) ex ey ey rfl).1

private theorem step_mono {S T : Finset ℕ} {t : ℕ} (h : S ⊆ T) : step t S ⊆ step t T :=
  union_subset_union h (image_subset_image h)

/-- Select progression-free outputs on one normalized residue class. -/
theorem normalized_gain (S : Finset ℕ) (weak : Weak 2 S) :
    ∃ U ⊆ step 2 S, ThreeAPFree (↑U : Set ℕ) ∧
      4*S.card ≤ 3*U.card+2*(pairs 2 S).card := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases empty : S=∅
    · subst S
      exact ⟨∅,empty_subset _,by simp,by simp⟩
    have ne := nonempty_iff_ne_empty.mpr empty
    let a := S.min' ne
    have ha := min'_mem S ne
    have lo (x) (hx : x ∈ S) : a ≤ x := min'_le _ x hx
    obtain ⟨C,shape,inside,closed⟩ := first_component S a ha lo weak
    obtain ⟨D,_,dC,freeD,gain⟩ := choice_table C shape
    let P := C.image (a+·)
    let E := D.image (a+·)
    let Q := S \ P
    have inj : Function.Injective (a+·) := fun x y eq => Nat.add_left_cancel eq
    have cP : P.card=C.card := card_image_of_injective _ inj
    have cE : E.card=D.card := card_image_of_injective _ inj
    have pS : P ⊆ S := by
      intro x hx
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
      exact inside j hj
    have qS : Q ⊆ S := sdiff_subset
    have root : 0 ∈ C := (by decide : ∀ V ∈ shapes, 0 ∈ V) C shape
    have ap : a ∈ P := mem_image.mpr ⟨0,root,by simp⟩
    have strict : Q ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨qS, by
      intro eq
      have ⟨_,h⟩ := mem_sdiff.mp (eq.symm ▸ ha : a ∈ Q)
      exact h ap⟩
    obtain ⟨V,vQ,fv,gv⟩ := ih Q strict (weak_mono qS weak)
    have uP : E ⊆ step 2 P := by
      intro X hX
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hX
      obtain ⟨i,hi,e|e⟩ := step_mem (dC hv)
      · exact mem_union_left _ (mem_image.mpr ⟨i,hi,by omega⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨a+i,mem_image.mpr ⟨i,hi,rfl⟩,by omega⟩)
    have fe : ThreeAPFree (↑E : Set ℕ) := by
      apply threeAPFree_iff_eq_right.mpr
      intro x hx y hy z hz eq
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
      have := freeD i hi j hj k hk (by omega)
      omega
    have sep (x) (xp : x ∈ P) (y) (yq : y ∈ Q) (cl : close 2 x y) : False := by
      obtain ⟨i,hi,rfl⟩ := mem_image.mp xp
      obtain ⟨ys,yn⟩ := mem_sdiff.mp yq
      exact yn (mem_image.mpr ⟨y-a,closed i hi y ys cl,by have := lo y ys; omega⟩)
    obtain ⟨free,disj⟩ := glue weak pS qS sep uP vQ fe fv
    refine ⟨E ∪ V,union_subset (uP.trans (step_mono pS)) (vQ.trans (step_mono qS)),free,?_⟩
    rw [card_union_of_disjoint disj,cE]
    have sz : Q.card+P.card=S.card := card_sdiff_add_card_eq_card pS
    have sub : pairs 2 Q ⊆ pairs 2 S := by
      intro x hx
      obtain ⟨hq,hy⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨qS hq,qS hy⟩
    by_cases tight : C=({0,2}:Finset ℕ)
    · have inS : a+2 ∈ S := inside _ (by simp [tight])
      have add : insert a (pairs 2 Q) ⊆ pairs 2 S :=
        insert_subset (mem_filter.mpr ⟨ha,inS⟩) sub
      have notin : a ∉ pairs 2 Q := fun h => (mem_sdiff.mp (mem_filter.mp h).1).2 ap
      have e := card_le_card add
      rw [card_insert_of_notMem notin] at e
      simp only [if_pos tight] at gain
      omega
    · have e := card_le_card sub
      simp only [if_neg tight] at gain
      omega

/-- Lower bound after adding one translate, valid at every integer displacement. -/
theorem integer_gain (A : Finset ℕ) (n t : ℕ) (ht : 0<t) (fit : A ⊆ range n)
    (weak : Weak t A) : 4*A.card ≤ 3*rothNumberNat (n+t)+2*(pairs t A).card := by
  classical
  let r (x : ℕ) := (2*x)%t
  let j (x : ℕ) := (2*x)/t
  let fiber (S : Finset ℕ) (b : ℕ) := S.filter (fun x => r x=b)
  let F (b : ℕ) := (fiber A b).image j
  have iden (x : ℕ) : r x+t*j x=2*x := Nat.mod_add_div (2*x) t
  have mono {x y : ℕ} (hr : r x=r y) (hj : j x=j y) : x=y := by
    have h := iden x
    rw [hr,hj,iden y] at h
    omega
  have shift (x : ℕ) : r (x+t)=r x ∧ j (x+t)=j x+2 := by
    dsimp only [r,j]
    rw [Nat.mul_add, Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ ht]
    exact ⟨rfl,rfl⟩
  have allr (x : ℕ) : r x ∈ range t := mem_range.mpr (Nat.mod_lt _ ht)
  have mass (S : Finset ℕ) : ∑ b ∈ range t, (fiber S b).card=S.card := by
    dsimp only [fiber]
    simp_rw [card_filter]
    rw [sum_comm]
    simp [allr]
  have spec {b i} (hi : i ∈ F b) : ∃ x ∈ A, r x=b ∧ j x=i := by
    obtain ⟨x,hx,e⟩ := mem_image.mp hi
    exact ⟨x,(mem_filter.mp hx).1,(mem_filter.mp hx).2,e⟩
  have weakF (b) : Weak 2 (F b) := by
    intro i hi k hk l hl e
    obtain ⟨x,hx,rx,rfl⟩ := spec hi
    obtain ⟨y,hy,ry,rfl⟩ := spec hk
    obtain ⟨z,hz,rz,rfl⟩ := spec hl
    have ix := iden x
    have iy := iden y
    have iz := iden z
    rw [rx] at ix
    rw [ry] at iy
    rw [rz] at iz
    have eq : x+z=y+y ∨ x+z=y+y+t ∨ x+z+t=y+y ∨
        x+z=y+y+2*t ∨ x+z+2*t=y+y := by
      rcases e with e|e|e|e|e <;>
        have et := congrArg (fun v => t*v) e <;>
        simp only [Nat.mul_add,Nat.reduceMul,Nat.mul_comm t 2,Nat.mul_comm t 4] at et <;> omega
    rcases weak x hx y hy z hz eq with h|h|h <;> simp [h]
  choose U hU freeU gain using fun b => normalized_gain (F b) (weakF b)
  let V := (step t A).filter (fun x => j x ∈ U (r x))
  have common {x y : ℕ} (c : close t x y) : r x=r y := by
    have em {a b k : ℕ} (e : 2*a+k*t=2*b) : r a=r b := by
      dsimp only [r]
      rw [← e,Nat.add_mul_mod_self_right]
    rcases c with e|e|e|e|e|e|e
    · rw [e]
    · exact em (k:=1) (by omega)
    · exact (em (k:=1) (by omega)).symm
    · exact em (k:=2) (by omega)
    · exact (em (k:=2) (by omega)).symm
    · exact em (k:=4) (by omega)
    · exact (em (k:=4) (by omega)).symm
  have fv : ThreeAPFree (↑V : Set ℕ) := by
    apply threeAPFree_iff_eq_right.mpr
    intro X hX Y hY Z hZ e
    obtain ⟨sx,ux⟩ := mem_filter.mp hX
    obtain ⟨sy,uy⟩ := mem_filter.mp hY
    obtain ⟨sz,uz⟩ := mem_filter.mp hZ
    obtain ⟨x,hx,ex⟩ := step_mem sx
    obtain ⟨y,hy,ey⟩ := step_mem sy
    obtain ⟨z,hz,ez⟩ := step_mem sz
    obtain ⟨xy,xz,_⟩ := projections_close weak hx hy hz ex ey ez e
    have tag {p P} (eq : P=p ∨ P=p+t) : r P=r p := by
      rcases eq with h|h <;> rw [h]
      exact (shift p).1
    have rr : r X=r Y := (tag ex).trans ((common xy).trans (tag ey).symm)
    have rs : r X=r Z := (tag ex).trans ((common xz).trans (tag ez).symm)
    have ix := iden X
    have iy := iden Y
    have iz := iden Z
    rw [← rr] at iy uy
    rw [← rs] at iz uz
    have eq : t*(j X+j Z)=t*(j Y+j Y) := by simp only [Nat.mul_add]; omega
    exact mono rs (threeAPFree_iff_eq_right.mp (freeU _) ux uy uz (Nat.eq_of_mul_eq_mul_left ht eq))
  have cap : V.card ≤ rothNumberNat (n+t) := by
    apply fv.le_rothNumberNat _ _ rfl
    intro X hx
    obtain ⟨x,ax,e|e⟩ := step_mem (mem_filter.mp hx).1 <;> have := mem_range.mp (fit ax) <;> omega
  have localBound (b : ℕ) : 4*(fiber A b).card ≤ 3*(fiber V b).card+2*(fiber (pairs t A) b).card := by
    have inj : Set.InjOn j (↑(fiber A b) : Set ℕ) := by
      intro x hx y hy eq
      exact mono ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) eq
    have cf : (F b).card=(fiber A b).card := card_image_of_injOn inj
    have cp : (pairs 2 (F b)).card ≤ (fiber (pairs t A) b).card := by
      have inc : pairs 2 (F b) ⊆ (fiber (pairs t A) b).image j := by
        intro i hi
        obtain ⟨h1,h2⟩ := mem_filter.mp hi
        obtain ⟨x,hx,rx,rfl⟩ := spec h1
        obtain ⟨y,hy,ry,jy⟩ := spec h2
        obtain ⟨rr,jj⟩ := shift x
        have sy : y=x+t := mono (ry.trans (rr.trans rx).symm) (jy.trans jj.symm)
        exact mem_image.mpr ⟨x,mem_filter.mpr ⟨mem_filter.mpr ⟨hx,sy ▸ hy⟩,rx⟩,rfl⟩
      exact (card_le_card inc).trans card_image_le
    have cu : (U b).card ≤ (fiber V b).card := by
      have inc : U b ⊆ (fiber V b).image j := by
        intro i ui
        obtain ⟨l,hl,e⟩ := step_mem (hU b ui)
        obtain ⟨x,hx,rx,rfl⟩ := spec hl
        have enter {y} (hy : y ∈ step t A) (rb : r y=b) (ji : j y=i) :
            i ∈ (fiber V b).image j := by
          exact mem_image.mpr ⟨y,mem_filter.mpr ⟨mem_filter.mpr ⟨hy,by simpa [rb,ji] using ui⟩,rb⟩,ji⟩
        rcases e with eq|eq
        · exact enter (mem_union_left _ hx) rx eq.symm
        · obtain ⟨rr,jj⟩ := shift x
          exact enter (mem_union_right _ (mem_image.mpr ⟨x,hx,rfl⟩)) (rr.trans rx) (jj.trans eq.symm)
      exact (card_le_card inc).trans card_image_le
    have g := gain b
    omega
  have all := sum_le_sum (s:=range t) (fun b _ => localBound b)
  simp only [sum_add_distrib,← mul_sum,mass] at all
  omega

/-- Two domino graphs together form a matching if genuine t-defects are absent. -/
theorem two_pair_bound (A : Finset ℕ) (t : ℕ) (ht : 0<t)
    (nod : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x<y → y<z →
      ¬(x+z=y+y ∨ x+z=y+y+t ∨ x+z+t=y+y)) :
    2*((pairs t A).card+(pairs (2*t) A).card) ≤ A.card := by
  let P := pairs t A
  let Q := pairs (2*t) A
  let E := P ∪ Q
  let f (x : ℕ) := if x ∈ P then x+t else x+2*t
  have ends {x} (h : x ∈ E) : x ∈ A ∧ f x ∈ A ∧ (f x=x+t ∨ f x=x+2*t) := by
    dsimp only [f]
    split_ifs with p
    · exact ⟨(mem_filter.mp p).1,(mem_filter.mp p).2,Or.inl rfl⟩
    · have q := (mem_union.mp h).resolve_left p
      exact ⟨(mem_filter.mp q).1,(mem_filter.mp q).2,Or.inr rfl⟩
  have bt {x y z} (ax : x ∈ A) (ay : y ∈ A) (az : z ∈ A)
      (xy : y=x+t ∨ y=x+2*t) (yz : z=y+t ∨ z=y+2*t) : False := by
    have h := nod x ax y ay z az (by omega) (by omega)
    omega
  have pq : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro x p q
    exact bt (mem_filter.mp p).1 (mem_filter.mp p).2 (mem_filter.mp q).2 (Or.inl rfl) (Or.inl (by omega))
  have inj : Set.InjOn f (↑E : Set ℕ) := by
    intro x hx y hy eq
    obtain ⟨ax,az,ex⟩ := ends hx
    obtain ⟨ay,_,ey⟩ := ends hy
    by_contra neq
    rcases lt_or_gt_of_ne neq with lt|lt
    · exact bt ax ay az (by left; omega) (by left; omega)
    · exact bt ay ax az (by left; omega) (by left; omega)
  have disj : Disjoint E (E.image f) := by
    rw [Finset.disjoint_left]
    intro y hy yy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp yy
    exact bt (ends hx).1 (ends hy).1 (ends hy).2.1 (ends hx).2.2 (ends hy).2.2
  have inc : E ∪ E.image f ⊆ A := by
    intro y hy
    rcases mem_union.mp hy with h|h
    · exact (ends h).1
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp h
      exact (ends hx).2.1
  have count := card_le_card inc
  rw [card_union_of_disjoint disj,card_image_of_injOn inj] at count
  have cE : E.card=P.card+Q.card := card_union_of_disjoint pq
  change 2*(P.card+Q.card) ≤ A.card
  omega

/-- A fixed chain of three exact defects gives a strict local cardinality loss. -/
theorem dyadic_defect_bound (A : Finset ℕ) (n t : ℕ) (ht : 0<t) (fit : A ⊆ range n)
    (weak1 : Weak t A) (weak2 : Weak (2*t) A) : 7*A.card ≤ 6*rothNumberNat (n+2*t) := by
  have g1 := integer_gain A n t ht fit weak1
  have g2 := integer_gain A n (2*t) (by omega) fit weak2
  have mono := rothNumberNat.monotone (show n+t ≤ n+2*t by omega)
  have comb := two_pair_bound A t ht (fun x hx y hy z hz hxy hyz e => by
    have h := weak1 x hx y hy z hz
    omega)
  omega

#print axioms integer_gain
#print axioms two_pair_bound
#print axioms dyadic_defect_bound

#print axioms first_component
#print axioms projections_close
#print axioms normalized_gain
end Erdos142DyadicClusters
