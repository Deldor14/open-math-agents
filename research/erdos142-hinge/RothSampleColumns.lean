import RothDigitCuts
import RothNineteenUpper

open Finset
namespace Erdos142DigitCuts

/-- K ordinary blocks suffice if their occupied residues represent every
    occupied residue anywhere at this scale. -/
def Sampled (A : Finset ℕ) (w K : ℕ) : Prop :=
  ∃ V : Finset ℕ, V.card≤K ∧ ∀ u<w, ∀ v, u+w*v ∈ A → ∃ z ∈ V, u+w*z ∈ A

/-- Fixing lower digits preserves a collection of representative blocks. -/
theorem restrict_sample {A : Finset ℕ} {u w s K : ℕ} (hu : u<w)
    (cover : Sampled A (w*s) K) : Sampled (slice A w u) s K := by
  obtain ⟨V,hv,hit⟩ := cover
  refine ⟨V,hv,?_⟩
  intro a ha b h
  have low : u+w*a<w*s := by
    have up := Nat.mul_le_mul_left w (Nat.succ_le_of_lt ha)
    rw [Nat.mul_succ] at up
    omega
  have e := (mem_slice hu).1 h
  have loc : u+w*a+w*s*b ∈ A := by convert e using 1; ring
  obtain ⟨z,hz,fit⟩ := hit (u+w*a) low b loc
  refine ⟨z,hz,(mem_slice hu).2 ?_⟩
  convert fit using 1
  ring

theorem sample_peel {A : Finset ℕ} {w K M : ℕ} (hw : 0<w) (cover : Sampled A w K)
    (free : ThreeAPFree (↑A : Set ℕ)) (cap : ∀ u<w, (slice A w u).card≤M) :
    A.card≤K*rothNumberNat w*M := by
  classical
  obtain ⟨V,size,hit⟩ := cover
  let low := A.image (fun x => x%w)
  let col (z : ℕ) := (range w).filter (fun u => u+w*z ∈ A)
  have ub (z : ℕ) : (col z).card≤rothNumberNat w := by
    have fr : ThreeAPFree (↑(col z) : Set ℕ) := by
      apply threeAPFree_iff_eq_right.mpr
      intro x hx y hy a ha eq
      have v := threeAPFree_iff_eq_right.mp free (mem_filter.mp hx).2 (mem_filter.mp hy).2
        (mem_filter.mp ha).2 (by omega)
      exact Nat.add_right_cancel v
    exact fr.le_rothNumberNat _ (fun _ h => mem_range.mp (mem_filter.mp h).1) rfl
  have incols : low ⊆ V.biUnion col := by
    intro u h
    obtain ⟨x,hx,rfl⟩ := mem_image.mp h
    have rep : x%w+w*(x/w) ∈ A := by simpa only [Nat.mod_add_div] using hx
    obtain ⟨z,hz,loc⟩ := hit _ (Nat.mod_lt x hw) _ rep
    exact mem_biUnion.mpr ⟨z,hz,mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt x hw),loc⟩⟩
  have small : low.card≤K*rothNumberNat w := calc
    _ ≤ (V.biUnion col).card := card_le_card incols
    _ ≤ ∑ z ∈ V, (col z).card := card_biUnion_le
    _ ≤ ∑ _z ∈ V, rothNumberNat w := sum_le_sum (fun z _ => ub z)
    _ ≤ _ := by simpa using Nat.mul_le_mul_right (rothNumberNat w) size
  let row (u : ℕ) := (slice A w u).image (fun v => u+w*v)
  have inside : A ⊆ low.biUnion row := by
    intro x hx
    have hu := Nat.mod_lt x hw
    exact mem_biUnion.mpr ⟨x%w,mem_image_of_mem _ hx,
      mem_image.mpr ⟨x/w,(mem_slice hu).2 (by simpa only [Nat.mod_add_div] using hx),Nat.mod_add_div _ _⟩⟩
  calc
    A.card ≤ (low.biUnion row).card := card_le_card inside
    _ ≤ ∑ u ∈ low, (row u).card := card_biUnion_le
    _ ≤ ∑ _u ∈ low, M := sum_le_sum (fun u h => by
      obtain ⟨x,_,rfl⟩ := mem_image.mp h
      exact card_image_le.trans (cap _ (Nat.mod_lt x hw)))
    _ ≤ _ := by simpa using Nat.mul_le_mul_right M small

def Samples (A : Finset ℕ) (low : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | (w,K)::xs => Sampled A (low*w) K ∧ Samples A (low*w) xs

private theorem restrict_samples {A : Finset ℕ} {w u : ℕ} (hu : u<w)
    (xs : List (ℕ × ℕ)) (low : ℕ) (g : Samples A (w*low) xs) :
    Samples (slice A w u) low xs := by
  induction xs generalizing low with
  | nil => trivial
  | cons pair xs ih =>
    obtain ⟨v,K⟩ := pair
    obtain ⟨c,tail⟩ := g
    rw [Nat.mul_assoc] at c tail
    exact ⟨restrict_sample hu c,ih _ tail⟩

/-- Every multicut product bound already holds for ordinary representative
    blocks, even when the samples at different cuts are chosen independently. -/
theorem sampled_multicut (xs : List (ℕ × ℕ)) (q : ℕ) (A : Finset ℕ)
    (pos : ∀ pair ∈ xs, 0<pair.1)
    (fit : A ⊆ range ((xs.map Prod.fst).prod*q)) (free : ThreeAPFree (↑A : Set ℕ))
    (g : Samples A 1 xs) :
    A.card ≤ (xs.map (fun pair => pair.2*rothNumberNat pair.1)).prod*rothNumberNat q := by
  induction xs generalizing A with
  | nil =>
    simp only [List.map_nil,List.prod_nil,one_mul] at fit ⊢
    exact free.le_rothNumberNat A (fun x h => mem_range.mp (fit h)) rfl
  | cons pair xs ih =>
    obtain ⟨w,K⟩ := pair
    obtain ⟨cover,tail⟩ := g
    rw [one_mul] at cover tail
    simp only [List.map_cons,List.prod_cons] at fit ⊢
    rw [Nat.mul_assoc] at fit ⊢
    apply sample_peel (pos (w,K) (by simp)) cover free
    intro u hu
    exact ih _ (fun p hp => pos p (List.mem_cons_of_mem _ hp)) (slice_range hu fit)
      (free_slice hu free) (restrict_samples hu xs 1 (by simpa using tail))

private theorem partition (n k : ℕ) : rothNumberNat (k*n) ≤ k*rothNumberNat n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul,Nat.succ_mul]
    exact (rothNumberNat_add_le _ _).trans (Nat.add_le_add_right ih _)

theorem seven_bit_capacity : rothNumberNat 128≤56 := by
  have h := partition 19 7
  rw [Erdos142FutureRecords.at_nineteen] at h
  exact (rothNumberNat.monotone (by decide : 128≤7*19)).trans h

#print axioms restrict_sample
#print axioms sample_peel
#print axioms sampled_multicut
#print axioms seven_bit_capacity
end Erdos142DigitCuts
