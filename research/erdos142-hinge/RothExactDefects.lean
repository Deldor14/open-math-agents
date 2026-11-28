import RothDefects

open Finset

namespace Erdos142ExactDefects

/-- A cover meets every genuine three-point support with the specified absolute defect. -/
def Covers (A C : Finset ℕ) (d : ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z →
    |(x : ℤ) + z - 2*y| = (d : ℤ) → x ∈ C ∨ y ∈ C ∨ z ∈ C

/-- Smaller endpoints of the pairs that can give a repeated projection. -/
def badStarts (A : Finset ℕ) (t : ℕ) : Finset ℕ :=
  A.filter fun x => ∃ y ∈ A, y = x+t ∨ y = x+2*t ∨ 2*y = 2*x+t

private theorem two_le_roth_two : 2 ≤ rothNumberNat 2 := by
  have free : ThreeAPFree ((range 2 : Finset ℕ) : Set ℕ) := by
    apply threeAPFree_iff_eq_right.mpr
    intro x hx y hy z hz he
    change x ∈ range 2 at hx
    change y ∈ range 2 at hy
    change z ∈ range 2 at hz
    simp only [mem_range] at hx hy hz
    omega
  exact free.le_rothNumberNat _ (fun _ hx => mem_range.mp hx) (by simp)

/-- Finite resilience inequality, for mathlib's actual finite Roth number. -/
theorem two_cover_bound (A C D : Finset ℕ) (n t : ℕ) (ht : 0 < t)
    (hn : A ⊆ range n) (hA : ThreeAPFree (↑A : Set ℕ))
    (hc : Covers A C t) (hd : Covers A D (2*t)) :
    2*A.card ≤ rothNumberNat (n+t) + 2*(C.card+D.card+(badStarts A t).card) := by
  let U := C ∪ D ∪ badStarts A t
  let B := A \ U
  have info {x} (hx : x ∈ B) : x ∈ A ∧ x ∉ C ∧ x ∉ D ∧ x ∉ badStarts A t := by
    simpa [B,U,not_or,and_assoc] using hx
  have sep {x y} (hx : x ∈ B) (hy : y ∈ B) :
      ¬(y = x+t ∨ y = x+2*t ∨ 2*y = 2*x+t) := by
    intro e
    exact (info hx).2.2.2 (mem_filter.mpr ⟨(info hx).1,y,(info hy).1,e⟩)
  have strong : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, ∀ j : ℤ, |j| ≤ 2*(1:ℤ) →
      (x:ℤ)+z-2*y=j*(t:ℤ) → x=z ∧ j=0 := by
    intro x hx y hy z hz j hj eq
    have ax := info hx
    have ay := info hy
    have az := info hz
    by_cases h0 : j=0
    · subst j
      exact ⟨threeAPFree_iff_eq_right.mp hA ax.1 ay.1 az.1 (by omega), rfl⟩
    exfalso
    have hj' := abs_le.mp hj
    have vals : j = -2 ∨ j = -1 ∨ j = 1 ∨ j = 2 := by omega
    have smallpair {a b} (ha : a ∈ B) (hb : b ∈ B) :
        ¬(b=a+t ∨ b=a+2*t ∨ 2*b=2*a+t ∨ a=b+t ∨ a=b+2*t ∨ 2*a=2*b+t) := by
      have f := sep ha hb
      have g := sep hb ha
      tauto
    have distinct : x ≠ y ∧ y ≠ z ∧ x ≠ z := by
      have p := smallpair hx hy
      have q := smallpair hx hz
      have r := smallpair hy hz
      rcases vals with h|h|h|h <;> rw [h] at eq <;> omega
    obtain ⟨a,b,c⟩ := distinct
    have no1 := hc x ax.1 y ay.1 z az.1 a b c
    have no2 := hd x ax.1 y ay.1 z az.1 a b c
    rw [eq] at no1 no2
    rcases vals with h|h|h|h <;> subst j <;>
      simp [abs_mul, abs_of_nonneg (Int.natCast_nonneg t)] at no1 no2 <;> tauto
  have fit : B ⊆ range n := fun _ hx => hn (info hx).1
  have expansion := Erdos142Defects.expansion_bound B n 1 t fit strong
  have low := Nat.mul_le_mul_left B.card two_le_roth_two
  have cU : U.card ≤ C.card + D.card + (badStarts A t).card :=
    (card_union_le (C ∪ D) _).trans (Nat.add_le_add_right (card_union_le C D) _)
  have cA : A.card ≤ B.card + U.card := by
    calc
      _ ≤ (B ∪ U).card := card_le_card (by intro x hx; by_cases h : x ∈ U <;> simp [B,h,hx])
      _ ≤ _ := card_union_le _ _
  simp only [one_mul, Nat.reduceAdd] at expansion
  omega

/-- Shift indices whose affine image meets a fixed free set form a free set. -/
theorem affine_partner_indices (A : Finset ℕ) (free : ThreeAPFree (↑A : Set ℕ))
    (L c u v : ℕ) (hc : 0 < c) (hv : 0 < v) :
    ((range L).filter (fun j => ∃ y ∈ A, c*y = u+v*j)).card ≤ rothNumberNat L := by
  let S := (range L).filter (fun j => ∃ y ∈ A, c*y = u+v*j)
  have good : ThreeAPFree (↑S : Set ℕ) := by
    apply threeAPFree_iff_eq_right.mpr
    intro i hi j hj k hk e
    obtain ⟨a,ha,ea⟩ := (mem_filter.mp hi).2
    obtain ⟨b,hb,eb⟩ := (mem_filter.mp hj).2
    obtain ⟨d,hd,ed⟩ := (mem_filter.mp hk).2
    have ee : c*(a+d)=c*(b+b) := by
      have ev := congrArg (fun s => v*s) e
      simp only [Nat.mul_add] at ev ⊢
      omega
    have ad := threeAPFree_iff_eq_right.mp free ha hb hd (Nat.eq_of_mul_eq_mul_left hc ee)
    subst d
    exact Nat.eq_of_mul_eq_mul_left hv (by omega)
  exact good.le_rothNumberNat _ (fun _ hx => mem_range.mp (mem_filter.mp hx).1) rfl

/-- Sum of the repeated-coordinate exceptions on any progression of shifts. -/
theorem sum_badStarts (A : Finset ℕ) (free : ThreeAPFree (↑A : Set ℕ))
    (L b q : ℕ) (hq : 0 < q) :
    ∑ j ∈ range L, (badStarts A (b+q*j)).card ≤ 3*A.card*rothNumberNat L := by
  classical
  let F (c u v : ℕ) := (range L).filter (fun j => ∃ y ∈ A, c*y=u+v*j)
  have per (x : ℕ) : ((range L).filter (fun j => x ∈ badStarts A (b+q*j))).card ≤
      3*rothNumberNat L := by
    have inc : (range L).filter (fun j => x ∈ badStarts A (b+q*j)) ⊆
        F 1 (x+b) q ∪ F 1 (x+2*b) (2*q) ∪ F 2 (2*x+b) q := by
      intro j hj
      obtain ⟨hj,hx⟩ := mem_filter.mp hj
      obtain ⟨y,hy,e|e|e⟩ := (mem_filter.mp hx).2
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hj,y,hy,by omega⟩))
      · apply mem_union_left _
        apply mem_union_right _
        exact mem_filter.mpr ⟨hj,y,hy,by rw [e]; ring⟩
      · exact mem_union_right _ (mem_filter.mpr ⟨hj,y,hy,by omega⟩)
    have h1 := affine_partner_indices A free L 1 (x+b) q (by decide) hq
    have h2 := affine_partner_indices A free L 1 (x+2*b) (2*q) (by decide) (by omega)
    have h3 := affine_partner_indices A free L 2 (2*x+b) q (by decide) hq
    have tot := (card_le_card inc).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
    dsimp only [F] at tot
    omega
  have decomp (j : ℕ) : (badStarts A (b+q*j)).card =
      ∑ x ∈ A, (if x ∈ badStarts A (b+q*j) then 1 else 0) := by
    rw [← Finset.card_filter]
    congr 1
    ext x
    simp [badStarts]
  simp_rw [decomp]
  rw [sum_comm]
  calc
    _ ≤ ∑ _x ∈ A, 3*rothNumberNat L := by
      apply sum_le_sum
      intro x _
      rw [← Finset.card_filter]
      exact per x
    _ = _ := by simp; ring

/-- In a half-open tube of width λt, a progression of outputs projecting modulo
    t has input defect zero or exactly ±t, for an arbitrary positive real slope. -/
theorem tube_projection (x y z t : ℤ) (ht : 0 < t) (s c X Y Z : ℝ) (hs : 0 < s)
    (hx : s*x+c ≤ X ∧ X < s*x+c+s*t)
    (hy : s*y+c ≤ Y ∧ Y < s*y+c+s*t)
    (hz : s*z+c ≤ Z ∧ Z < s*z+c+s*t)
    (ap : X+Z=2*Y) (hmod : t ∣ x+z-2*y) :
    x+z-2*y=0 ∨ x+z-2*y=t ∨ x+z-2*y= -t := by
  obtain ⟨j,hj⟩ := hmod
  have bounds : -(2*(t:ℝ)) < (x:ℝ)+z-2*y ∧ (x:ℝ)+z-2*y < 2*t := by
    constructor
    · apply lt_of_mul_lt_mul_left (a := s) _ hs.le
      linarith only [hx.2, hz.2, hy.1, ap]
    · apply lt_of_mul_lt_mul_left (a := s) _ hs.le
      linarith only [hx.1, hz.1, hy.2, ap]
  have lo : -(2*t) < x+z-2*y := by exact_mod_cast bounds.1
  have hi : x+z-2*y < 2*t := by exact_mod_cast bounds.2
  rw [hj] at lo hi ⊢
  have low : -2 < j := by
    apply lt_of_mul_lt_mul_left (a := t) _ ht.le
    linarith only [lo]
  have high : j < 2 := by
    apply lt_of_mul_lt_mul_left (a := t) _ ht.le
    linarith only [hi]
  have vals : j=0 ∨ j=1 ∨ j= -1 := by omega
  rcases vals with h|h|h <;> simp [h]

/-- With one exact defect absent even for repeated coordinates, one can take
    an independent digit in every fiber at any integer dilation. -/
theorem single_defect_product (B : Finset ℕ) (n k t : ℕ) (hk : 0 < k) (ht : 0 < t)
    (fit : B ⊆ range n)
    (strong : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B,
      (let d := (x:ℤ)+z-2*y; d=0 ∨ d=t ∨ d= -(t:ℤ)) → x=y ∧ y=z) :
    B.card * rothNumberNat k ≤ rothNumberNat (k*n+(k-1)*t) := by
  obtain ⟨S,hS,cS,fS⟩ := rothNumberNat_spec k
  let lift (p : ℕ × ℕ) := p.1 + t*(((k-1)*p.1)/t+p.2)
  have rep (x i : ℕ) : lift (x,i) + ((k-1)*x)%t = k*x+t*i := by
    have h := Nat.mod_add_div ((k-1)*x) t
    have hk' : k = (k-1)+1 := by omega
    dsimp only [lift]
    rw [Nat.mul_add]
    have kx : k*x = (k-1)*x+x := by conv_lhs => rw [hk',Nat.add_mul,Nat.one_mul]
    omega
  have tube {x i : ℕ} (hi : i ∈ S) :
      (k:ℝ)*x+(1-(t:ℝ)) ≤ lift (x,i) ∧ (lift (x,i):ℝ) < (k:ℝ)*x+(1-(t:ℝ))+(k:ℝ)*t := by
    have ir := mem_range.mp (hS hi)
    have rem := Nat.mod_lt ((k-1)*x) ht
    have e := rep x i
    have ri : t*i ≤ t*(k-1) := Nat.mul_le_mul_left _ (by omega)
    have rt : t*(k-1) + t = k*t := by
      rw [← Nat.mul_succ, Nat.mul_comm]
      congr 1
      omega
    have a : k*x < lift (x,i)+t := by omega
    have b : lift (x,i)+t ≤ k*x+k*t := by omega
    have a' : (k:ℝ)*x+1 ≤ lift (x,i)+(t:ℝ) := by exact_mod_cast Nat.succ_le_of_lt a
    have b' : (lift (x,i):ℝ)+t ≤ (k:ℝ)*x+(k:ℝ)*t := by exact_mod_cast b
    constructor <;> linarith
  let U := (B ×ˢ S).image lift
  have proj {x y z i j l : ℕ} (hx : x ∈ B) (hy : y ∈ B) (hz : z ∈ B)
      (hi : i ∈ S) (hj : j ∈ S) (hl : l ∈ S)
      (eq : lift (x,i)+lift (z,l)=lift (y,j)+lift (y,j)) : x=y ∧ y=z := by
    have cong : (t:ℤ) ∣ (x:ℤ)+z-2*y := by
      dsimp only [lift] at eq
      have e : (x:ℤ)+(t:ℤ)*(((((k-1)*x)/t+i : ℕ):ℤ))+
          (z+(t:ℤ)*(((((k-1)*z)/t+l : ℕ):ℤ))) =
          y+(t:ℤ)*(((((k-1)*y)/t+j : ℕ):ℤ))+
          (y+(t:ℤ)*(((((k-1)*y)/t+j : ℕ):ℤ))) := by exact_mod_cast eq
      use 2*(((((k-1)*y)/t+j : ℕ):ℤ))-(((((k-1)*x)/t+i : ℕ):ℤ))-(((((k-1)*z)/t+l : ℕ):ℤ))
      linarith
    exact strong x hx y hy z hz (tube_projection x y z t (by exact_mod_cast ht) k
      (1-(t:ℝ)) _ _ _ (by exact_mod_cast hk) (by push_cast; simpa using tube hi)
      (by push_cast; simpa using tube hj) (by push_cast; simpa using tube hl)
      (by exact_mod_cast (by omega : lift (x,i)+lift (z,l)=2*lift (y,j)))
      cong)
  have inj : Set.InjOn lift (↑(B ×ˢ S) : Set (ℕ × ℕ)) := by
    rintro ⟨x,i⟩ xi ⟨y,j⟩ yj e
    obtain ⟨hx,hi⟩ := mem_product.mp xi
    obtain ⟨hy,hj⟩ := mem_product.mp yj
    have xy : x = y := (proj hx hy hy hi hj hj (by rw [e])).1
    subst y
    dsimp only [lift] at e
    have ij : i=j := Nat.add_left_cancel (Nat.eq_of_mul_eq_mul_left ht (Nat.add_left_cancel e))
    rw [ij]
  have free : ThreeAPFree (↑U : Set ℕ) := by
    apply threeAPFree_iff_eq_right.mpr
    intro a ha b hb c hc e
    obtain ⟨⟨x,i⟩,xi,rfl⟩ := mem_image.mp ha
    obtain ⟨⟨y,j⟩,yj,rfl⟩ := mem_image.mp hb
    obtain ⟨⟨z,l⟩,zl,rfl⟩ := mem_image.mp hc
    obtain ⟨hx,hi⟩ := mem_product.mp xi
    obtain ⟨hy,hj⟩ := mem_product.mp yj
    obtain ⟨hz,hl⟩ := mem_product.mp zl
    have xyz : x=y ∧ y=z := proj hx hy hz hi hj hl e
    obtain ⟨rfl,rfl⟩ := xyz
    have ee : t*(i+l)=t*(j+j) := by
      dsimp only [lift] at e
      simp only [Nat.mul_add] at e ⊢
      omega
    have il : i=l := threeAPFree_iff_eq_right.mp fS hi hj hl (Nat.eq_of_mul_eq_mul_left ht ee)
    rw [il]
  have sizeU : U.card=B.card*rothNumberNat k := by
    rw [card_image_of_injOn inj,card_product,cS]
  rw [← sizeU]
  apply free.le_rothNumberNat _ _ rfl
  intro a ha
  obtain ⟨⟨x,i⟩,xi,rfl⟩ := mem_image.mp ha
  obtain ⟨hx,hi⟩ := mem_product.mp xi
  have xn : k*x < k*n := Nat.mul_lt_mul_of_pos_left (mem_range.mp (fit hx)) hk
  have it := Nat.mul_le_mul_left t (show i ≤ k-1 by have := mem_range.mp (hS hi); omega)
  have eq := rep x i
  rw [Nat.mul_comm t (k-1)] at it
  omega

/-- Removing a cover and the smaller endpoints removes all repeated projections as well. -/
theorem cleaned_strong (A C : Finset ℕ) (t : ℕ) (ht : 0 < t)
    (free : ThreeAPFree (↑A : Set ℕ)) (hc : Covers A C t) :
    let B := A \ (C ∪ badStarts A t)
    ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B,
      (let d := (x:ℤ)+z-2*y; d=0 ∨ d=t ∨ d= -(t:ℤ)) → x=y ∧ y=z := by
  let U := C ∪ badStarts A t
  let B := A \ U
  have info {x} (hx : x ∈ B) : x ∈ A ∧ x ∉ C ∧ x ∉ badStarts A t := by
    simpa [B,U,not_or] using hx
  have sep {x y} (hx : x ∈ B) (hy : y ∈ B) :
      ¬(y = x+t ∨ y = x+2*t ∨ 2*y = 2*x+t) := by
    intro e
    exact (info hx).2.2 (mem_filter.mpr ⟨(info hx).1,y,(info hy).1,e⟩)
  dsimp only
  intro x hx y hy z hz e
  obtain ⟨ax,cx,_⟩ := info hx
  obtain ⟨ay,cy,_⟩ := info hy
  obtain ⟨az,cz,_⟩ := info hz
  rcases e with e|e
  · have eq := threeAPFree_iff_eq_right.mp free ax ay az (by omega : x+z=y+y)
    omega
  exfalso
  have ab := sep hx hy
  have ba := sep hy hx
  have ac := sep hx hz
  have ca := sep hz hx
  have bc := sep hy hz
  have cb := sep hz hy
  have ends : x ≠ y ∧ y ≠ z ∧ x ≠ z := by rcases e with e|e <;> omega
  obtain ⟨a,b,c⟩ := ends
  have absD : |(x:ℤ)+z-2*y| = (t:ℤ) := by rcases e with h|h <;> simp [h]
  exact (hc x ax y ay z az a b c absD).elim cx (Or.elim · cy cz)

/-- Any small cover for one exact defect transfers the rest of the set to every
    integer dilation. Repeated input coordinates are charged to bad starts. -/
theorem single_cover_transfer (A C : Finset ℕ) (n k t : ℕ) (hk : 0 < k) (ht : 0 < t)
    (fit : A ⊆ range n) (free : ThreeAPFree (↑A : Set ℕ)) (hc : Covers A C t) :
    A.card * rothNumberNat k ≤ rothNumberNat (k*n+(k-1)*t) +
      (C.card+(badStarts A t).card)*rothNumberNat k := by
  let U := C ∪ badStarts A t
  let B := A \ U
  have info {x} (hx : x ∈ B) : x ∈ A ∧ x ∉ C ∧ x ∉ badStarts A t := by
    simpa [B,U,not_or] using hx
  have strong := cleaned_strong A C t ht free hc
  have transfer := single_defect_product B n k t hk ht (fun _ hx => fit (info hx).1) strong
  have cA : A.card ≤ B.card + (C.card+(badStarts A t).card) := by
    calc
      _ ≤ (B ∪ U).card := card_le_card (by intro x hx; by_cases h : x ∈ U <;> simp [B,h,hx])
      _ ≤ B.card + U.card := card_union_le _ _
      _ ≤ _ := Nat.add_le_add_left (card_union_le _ _) _
  have sz := Nat.mul_le_mul_right (rothNumberNat k) cA
  rw [Nat.add_mul] at sz
  omega

/-- Counts shifts on any arithmetic progression for which both targets have
    small covers. This finite bound has no typical-length assumption. -/
theorem rare_shifts (A : Finset ℕ) (C : ℕ → Finset ℕ) (n L b q T a K : ℕ)
    (hb : 0 < b) (hq : 0 < q) (bound : ∀ j < L, b+q*j ≤ T)
    (fit : A ⊆ range n) (free : ThreeAPFree (↑A : Set ℕ))
    (covers : ∀ d, Covers A (C d) d)
    (gain : K+rothNumberNat (n+T)+4*a ≤ 2*A.card) :
    ((range L).filter (fun j => (C (b+q*j)).card ≤ a ∧
      (C (2*(b+q*j))).card ≤ a)).card*K ≤ 6*A.card*rothNumberNat L := by
  let S := (range L).filter (fun j => (C (b+q*j)).card ≤ a ∧ (C (2*(b+q*j))).card ≤ a)
  calc
    S.card*K = ∑ _j ∈ S, K := by simp
    _ ≤ ∑ j ∈ S, 2*(badStarts A (b+q*j)).card := by
      apply sum_le_sum
      intro j hj
      obtain ⟨jl,h1,h2⟩ := mem_filter.mp hj
      have tT := bound j (mem_range.mp jl)
      have ht : 0 < b+q*j := by omega
      have E := two_cover_bound A (C (b+q*j)) (C (2*(b+q*j))) n (b+q*j)
        ht fit free (covers _) (covers _)
      have mono := rothNumberNat.monotone (show n+(b+q*j) ≤ n+T by omega)
      omega
    _ ≤ ∑ j ∈ range L, 2*(badStarts A (b+q*j)).card :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; omega)
    _ ≤ _ := by
      rw [← mul_sum]
      have total := sum_badStarts A free L b q hq
      nlinarith only [total]

#print axioms two_cover_bound
#print axioms affine_partner_indices
#print axioms sum_badStarts
#print axioms tube_projection
#print axioms single_defect_product
#print axioms single_cover_transfer
#print axioms rare_shifts

end Erdos142ExactDefects
