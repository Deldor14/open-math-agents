import RothRamseyGlue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset
namespace Erdos142SparseRepair
variable {ι : Type*} [DecidableEq ι]

def mass (z : ℝ) (F : Finset (Finset ι)) : ℝ := ∑ s ∈ F, z ^ s.card

def occupied (F : Finset (Finset ι)) (v : ι) := F.filter (fun s => v ∈ s)

def available (F : Finset (Finset ι)) (v : ι) :=
  F.filter (fun s => v ∉ s ∧ insert v s ∈ F)

def eligible (F : Finset (Finset ι)) (v : ι) :=
  occupied F v ∪ available F v

/-- Exact occupation identity for a hereditary finite family. Eligibility means
    that all other occupied sites allow v to be present. -/
theorem toggle {F : Finset (Finset ι)} (v : ι) (down : ∀ s ∈ F, s.erase v ∈ F) (z : ℝ) :
    (1+z)*mass z (occupied F v) = z*mass z (eligible F v) := by
  classical
  have bij : (available F v).image (insert v) = occupied F v := by
    ext s
    constructor
    · rintro hs
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hs
      exact mem_filter.mpr ⟨(mem_filter.mp ht).2.2,mem_insert_self _ _⟩
    · intro hs
      obtain ⟨hin,hv⟩ := mem_filter.mp hs
      refine mem_image.mpr ⟨s.erase v,mem_filter.mpr ⟨down _ hin,
        notMem_erase _ _,?_⟩, insert_erase hv⟩
      simpa only [insert_erase hv] using hin
  have inj : Set.InjOn (insert v) (↑(available F v) : Set (Finset ι)) := by
    intro s hs t ht eq
    have e := congrArg (fun a : Finset ι => a.erase v) eq
    simpa only [erase_insert (mem_filter.mp hs).2.1,erase_insert (mem_filter.mp ht).2.1] using e
  have occ : mass z (occupied F v)=z*mass z (available F v) := by
    rw [mass,←bij,sum_image inj,mass,mul_sum]
    apply sum_congr rfl
    intro s hs
    rw [card_insert_of_notMem (mem_filter.mp hs).2.1,pow_succ,mul_comm]
  have dis : Disjoint (occupied F v) (available F v) := by
    apply disjoint_left.mpr
    intro s hs ht
    exact (mem_filter.mp ht).2.1 ((mem_filter.mp hs).2)
  have both : mass z (eligible F v)=mass z (occupied F v)+mass z (available F v) := by
    unfold eligible mass
    rw [sum_union dis]
  rw [both]
  linarith

theorem occupation_upper {F : Finset (Finset ι)}
    (v : ι) (down : ∀ s ∈ F, s.erase v ∈ F) {z : ℝ} (hz : 0≤z) :
    (1+z)*mass z (occupied F v) ≤ z*mass z F := by
  rw [toggle v down]
  apply mul_le_mul_of_nonneg_left _ hz
  apply sum_le_sum_of_subset_of_nonneg
  · intro s hs
    rcases mem_union.mp hs with ha|ha <;> exact (mem_filter.mp ha).1
  · intro s _ _
    exact pow_nonneg hz _

/-- Two prescribed vertices cost two factors of the Bernoulli parameter. -/
theorem pair_upper {F : Finset (Finset ι)} (down : ∀ s ∈ F, ∀ t ⊆ s, t ∈ F)
    {v w : ι} (ne : v≠w) {z : ℝ} (hz : 0≤z) :
    (1+z)^2*mass z (occupied (occupied F v) w) ≤ z^2*mass z F := by
  have first := occupation_upper v (F:=F) (fun s hs => down _ hs _ (erase_subset _ _)) hz
  have second := occupation_upper w (F:=occupied F v) (fun s hs =>
    mem_filter.mpr ⟨down _ (mem_filter.mp hs).1 _ (erase_subset _ _),
      (mem_erase.mpr ⟨ne,(mem_filter.mp hs).2⟩)⟩) hz
  calc
    _ = (1+z)*((1+z)*mass z (occupied (occupied F v) w)) := by ring
    _ ≤ (1+z)*(z*mass z (occupied F v)) := mul_le_mul_of_nonneg_left second (by linarith)
    _ = z*((1+z)*mass z (occupied F v)) := by ring
    _ ≤ z*(z*mass z F) := mul_le_mul_of_nonneg_left first hz
    _ = _ := by ring

/-- A link certificate bounds the failure of the lower occupancy marginal. -/
theorem occupation_lower {F : Finset (Finset ι)} (v : ι)
    (down : ∀ s ∈ F, s.erase v ∈ F) (link : Finset (Finset ι))
    (witness : ∀ s ∈ F, s ∉ eligible F v → ∃ e ∈ link, e ⊆ s)
    {z : ℝ} (hz : 0≤z) :
    z*mass z F ≤ (1+z)*mass z (occupied F v) +
      z*(∑ e ∈ link, mass z (F.filter (fun s => e ⊆ s))) := by
  classical
  have cap : mass z F ≤ mass z (eligible F v) +
      ∑ e ∈ link, mass z (F.filter (fun s => e ⊆ s)) := by
    have es : eligible F v ⊆ F := fun s hs =>
      (mem_union.mp hs).elim (fun h => (mem_filter.mp h).1) (fun h => (mem_filter.mp h).1)
    have ident : mass z (eligible F v)=
        ∑ s ∈ F, (if s ∈ eligible F v then z^s.card else 0) := by
      rw [←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr es]
      rfl
    simp only [mass,sum_filter] at ident ⊢
    rw [ident,sum_comm,←sum_add_distrib]
    apply sum_le_sum
    intro s hs
    by_cases hel : s ∈ eligible F v
    · simp only [if_pos hel,le_add_iff_nonneg_right]
      apply sum_nonneg
      intro e _
      split <;> positivity
    · obtain ⟨e,he,sub⟩ := witness s hs hel
      simp only [if_neg hel,zero_add]
      calc
        _ = (if e ⊆ s then z^s.card else 0) := by simp [sub]
        _ ≤ _ := single_le_sum (f:=fun e : Finset ι => if e ⊆ s then z^s.card else 0)
          (fun e _ => by split <;> positivity) he
  rw [toggle v down,←mul_add]
  exact mul_le_mul_of_nonneg_left cap hz

/-- Each long progression contains one complete aligned shorter block,
    with alignment measured on its own residue chain. -/
theorem aligned_block {L h q a N : ℕ} (hh : 0<h) (len : 2*h≤L) (pos : 0<q)
    (fits : ∀ i<L, a+i*q<N) :
    ∃ j, j<h ∧ ((a+j*q)/q)%h=0 ∧ ∀ i<h, j+i<L ∧ a+(j+i)*q<N := by
  let j := (h-(a/q)%h)%h
  have bound : j<h := Nat.mod_lt _ hh
  refine ⟨j,bound,?_,?_⟩
  · rw [Nat.add_mul_div_right _ _ pos]
    have hm : (a/q)%h<h := Nat.mod_lt _ hh
    change ((a/q)+(h-(a/q)%h)%h)%h=0
    rw [Nat.add_mod_mod]
    have eq : (a/q)+(h-(a/q)%h) = h*((a/q)/h+1) := by
      have reconstruct := Nat.mod_add_div (a/q) h
      rw [Nat.mul_add,Nat.mul_one]
      omega
    simp [eq]
  · intro i hi
    have hj : j+i<L := by omega
    exact ⟨hj,fits _ hj⟩

/-- Delete just the old vertices implicated in a mixed triple. An affirmative
    test for a vertex only examines triples with another vertex in the blocker. -/
def repair (S B : Finset ℕ) : Finset ℕ :=
  S.filter (fun x => ∀ b ∈ B, ∀ y ∈ S ∪ B, x≠b → x≠y → b≠y →
    x+b≠y+y ∧ x+y≠b+b ∧ b+y≠x+x)

theorem repair_free {k : ℕ} (hk : 3≤k) (S B : Finset ℕ)
    (sf : Erdos142LongDigits.Free k S) (bf : Erdos142LongDigits.Free 3 B) :
    Erdos142LongDigits.Free k (repair S B ∪ B) := by
  classical
  let A := repair S B ∪ B
  let tag (x : ℕ) := decide (x ∈ B)
  let seed (i : Bool) := if i then B else S
  have belongs {x : ℕ} (hx : x ∈ A) : x ∈ S ∪ B := by
    rcases mem_union.mp hx with hs|hb
    · exact mem_union_left _ (mem_filter.mp hs).1
    · exact mem_union_right _ hb
  have old {x : ℕ} (hx : x ∈ A) (out : x ∉ B) : x ∈ repair S B :=
    (mem_union.mp hx).resolve_right out
  have test {x b y : ℕ} (hx : x ∈ A) (out : x ∉ B) (hb : b ∈ B)
      (hy : y ∈ A) (nxy : x≠y) (nby : b≠y) :=
    (mem_filter.mp (old hx out)).2 b hb y (belongs hy) (fun e => out (e ▸ hb)) nxy nby
  apply Erdos142RamseyGlue.free_glue hk A tag seed
  · intro x hx
    by_cases h : x ∈ B
    · simp [seed,tag,h]
    · simpa [seed,tag,h] using (mem_filter.mp (old hx h)).1
  · intro i
    cases i with
    | false => exact sf
    | true => exact fun a q hq terms => bf a q hq (fun j hj => terms j (by omega))
  · intro x hx y hy z hz eq
    by_cases same : x=y
    · have ez : z=y := by omega
      simp [same,ez]
    have nyz : y≠z := by omega
    have nxz : x≠z := by omega
    by_cases bx : x ∈ B <;> by_cases byy : y ∈ B <;> by_cases bz : z ∈ B
    all_goals simp [tag,bx,byy,bz]
    · exact (test hz bz byy hx nxz.symm (Ne.symm same)).2.1 (by omega)
    · exact (test hy byy bx hz nyz nxz).2.2 eq
    · exact (test hy byy bx hz nyz nxz).2.2 eq
    · exact (test hx bx byy hz nxz nyz).2.1 eq
    · exact (test hx bx byy hz nxz nyz).2.1 eq
    · exact (test hx bx bz hy same nyz.symm).1 eq

#print axioms repair_free
#print axioms pair_upper
#print axioms occupation_lower
#print axioms toggle
#print axioms occupation_upper
#print axioms aligned_block
end Erdos142SparseRepair
