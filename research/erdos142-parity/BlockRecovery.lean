import MORWindows

/-! Block restrictions of arbitrary k-AP-free sets. The total shortfall from
local maximum size bounds how many blocks must be pruned and the number of
points in those blocks. The partition arity may grow with the top scale. -/
namespace Erdos142Blocks
open ProgressionParity Set.IsAPOfLengthFree Finset

def part (A : Finset ℕ) (m i : ℕ) : Finset ℕ :=
  (Icc 1 m).filter fun x => i*m+x ∈ A

lemma part_free {k : ℕ} (A : Finset ℕ) (fa : Free (· ∈ A) k) (m i : ℕ) :
    Free (· ∈ part A m i) k := by
  intro a d hd run
  apply fa (i*m+a) d hd
  apply (run_iff_forall _ _ _ _).mpr
  intro t ht
  simpa [Nat.add_assoc] using (mem_filter.mp ((run_iff_forall _ _ _ _).mp run t ht)).2

lemma part_upper {k : ℕ} (hk : 1 < k) (A : Finset ℕ) (fa : Free (· ∈ A) k) (m i : ℕ) :
    (part A m i).card ≤ maxCard k m :=
  bound_witness hk _ (filter_subset _ _) (part_free A fa m i)

theorem sum_parts {q m : ℕ} (hm : 0 < m) (A : Finset ℕ) (ha : A ⊆ Icc 1 (q*m)) :
    ∑ i ∈ range q, (part A m i).card = A.card := by
  let f := fun x : ℕ => (x-1)/m
  have main := @card_eq_sum_card_fiberwise ℕ ℕ _ f A (range q) (by
    intro x hx
    obtain ⟨lx,ux⟩ := mem_Icc.mp (ha hx)
    exact mem_range.mpr ((Nat.div_lt_iff_lt_mul hm).mpr (by omega)))
  rw [main]
  apply sum_congr rfl
  intro i _
  have eq : (part A m i).image (i*m+·) = A.filter (f · = i) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
      obtain ⟨hy,ay⟩ := mem_filter.mp hy
      obtain ⟨lo,hi⟩ := mem_Icc.mp hy
      refine mem_filter.mpr ⟨ay,?_⟩
      dsimp [f]
      rw [show i*m+y-1=m*i+(y-1) by rw [Nat.mul_comm m i];omega,
        Nat.mul_add_div hm,Nat.div_eq_of_lt (by omega)]
      simp
    · intro hx
      obtain ⟨ax,ix⟩ := mem_filter.mp hx
      have pos := (mem_Icc.mp (ha ax)).1
      have d := Nat.mod_add_div (x-1) m
      change (x-1)/m=i at ix
      rw [ix,Nat.mul_comm m i] at d
      have h := Nat.mod_lt (x-1) hm
      have eq : i*m+((x-1)%m+1)=x := by omega
      exact mem_image.mpr ⟨(x-1)%m+1,mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,by rw [eq];exact ax⟩,eq⟩
  rw [← eq,card_image_of_injective _ (fun x y h => Nat.add_left_cancel h)]

/-- The local shortfalls are nonnegative and add up to an exact global deficit. -/
theorem deficit_sum {k q m : ℕ} (hk : 1 < k) (hm : 0 < m) (A : Finset ℕ)
    (ha : A ⊆ Icc 1 (q*m)) (fa : Free (· ∈ A) k) :
    ∑ i ∈ range q, (maxCard k m-(part A m i).card) = q*maxCard k m-A.card := by
  have h : ∑ i ∈ range q, ((maxCard k m-(part A m i).card)+(part A m i).card) =
      q*maxCard k m := by
    calc _ = ∑ _i ∈ range q, maxCard k m := by
           apply sum_congr rfl
           intro i _
           exact Nat.sub_add_cancel (part_upper hk A fa m i)
         _ = _ := by simp
  rw [sum_add_distrib,sum_parts hm A ha] at h
  omega

/-- Every block extends to an inclusion-maximal free set. -/
theorem maximal_extension {k m : ℕ} (B : Finset ℕ) (hb : B ⊆ Icc 1 m)
    (fb : Free (· ∈ B) k) :
    ∃ D : Finset ℕ, B ⊆ D ∧ D ⊆ Icc 1 m ∧ Free (· ∈ D) k ∧
      ∀ C : Finset ℕ, D ⊆ C → C ⊆ Icc 1 m → Free (· ∈ C) k → C=D := by
  classical
  let S := (Icc 1 m).powerset.filter fun C => B ⊆ C ∧ Free (· ∈ C) k
  have b : B ∈ S := mem_filter.mpr ⟨mem_powerset.mpr hb,Subset.rfl,fb⟩
  obtain ⟨D,hd,high⟩ := S.exists_max_image card ⟨B,b⟩
  obtain ⟨hd,bd,fd⟩ := mem_filter.mp hd
  refine ⟨D,bd,mem_powerset.mp hd,fd,?_⟩
  intro C dc hc fc
  have cmp := high C (mem_filter.mpr ⟨mem_powerset.mpr hc,bd.trans dc,fc⟩)
  exact (Finset.eq_of_subset_of_card_le dc cmp).symm

/-- A global lower bound suffices to recover every block from a local maximal
set within the indicated absolute deficit. No unproved extremal value enters. -/
theorem exact_recovery {k q m B : ℕ} (hk : 1 < k) (hm : 0 < m) (A : Finset ℕ)
    (ha : A ⊆ Icc 1 (q*m)) (fa : Free (· ∈ A) k) (hB : B ≤ A.card)
    {i : ℕ} (hi : i < q) :
    ∃ D : Finset ℕ, part A m i ⊆ D ∧ D ⊆ Icc 1 m ∧ Free (· ∈ D) k ∧
      maxCard k m-D.card ≤ q*maxCard k m-B ∧
      ∀ C : Finset ℕ, D ⊆ C → C ⊆ Icc 1 m → Free (· ∈ C) k → C=D := by
  obtain ⟨D,d,sub,fre,mx⟩ := maximal_extension (part A m i) (filter_subset _ _) (part_free A fa m i)
  have le := single_le_sum (f := fun j => maxCard k m-(part A m j).card)
    (fun _ _ => Nat.zero_le _) (mem_range.mpr hi)
  rw [deficit_sum hk hm A ha fa] at le
  have cc := card_le_card d
  exact ⟨D,d,sub,fre,by omega,mx⟩

def deficient (A : Finset ℕ) (q m R t : ℕ) : Finset ℕ :=
  (range q).filter fun i => t < R-(part A m i).card

/-- Dropping every block farther than t from local optimality loses at most the
following number of points; the estimate is simultaneous over all blocks. -/
theorem trim_cost {k q m : ℕ} (hk : 1 < k) (hm : 0 < m) (A : Finset ℕ)
    (ha : A ⊆ Icc 1 (q*m)) (fa : Free (· ∈ A) k) (t : ℕ) :
    (t+1)*(∑ i ∈ deficient A q m (maxCard k m) t, (part A m i).card) ≤
      (maxCard k m-(t+1))*(q*maxCard k m-A.card) := by
  let R := maxCard k m
  let S := deficient A q m R t
  have major (i : ℕ) (hi : i∈S) :
      (t+1)*(part A m i).card ≤ (R-(t+1))*(R-(part A m i).card) := by
    have bad := (mem_filter.mp hi).2
    change t < R-(part A m i).card at bad
    calc _ ≤ (t+1)*(R-(t+1)) := Nat.mul_le_mul_left _ (by omega)
         _ = (R-(t+1))*(t+1) := Nat.mul_comm _ _
         _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have count : ∑ i ∈ S,(R-(part A m i).card) ≤ q*R-A.card := by
    calc _ ≤ ∑ i ∈ range q,(R-(part A m i).card) :=
           sum_le_sum_of_subset (filter_subset _ _)
         _ = _ := deficit_sum hk hm A ha fa
  change (t+1)*(∑ i ∈ S, (part A m i).card) ≤ (R-(t+1))*(q*R-A.card)
  calc _ = ∑ i ∈ S,(t+1)*(part A m i).card := mul_sum ..
       _ ≤ ∑ i ∈ S,(R-(t+1))*(R-(part A m i).card) := sum_le_sum major
       _ = _ := (mul_sum ..).symm
       _ ≤ _ := Nat.mul_le_mul_left _ count

end Erdos142Blocks
#print axioms Erdos142Blocks.exact_recovery
#print axioms Erdos142Blocks.trim_cost
