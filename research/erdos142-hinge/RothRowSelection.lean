import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open Finset
namespace Erdos142RowSelection

/-- A row accepts a prescribed subset of possible shifts. -/
def hits {ι Ω : Type*} [Fintype ι] [DecidableEq Ω] (C : ι → Finset Ω) (σ : ι → Ω) :=
  univ.filter (fun i => σ i ∈ C i)

private def pattern {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
    (C : ι → Finset Ω) (H : Finset ι) :=
  Fintype.piFinset (fun i => if i ∈ H then C i else (C i)ᶜ)

private theorem mem_pattern {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
    (C : ι → Finset Ω) (H : Finset ι) (σ : ι → Ω) :
    σ ∈ pattern C H ↔ hits C σ=H := by
  rw [pattern,Fintype.mem_piFinset]
  constructor
  · intro h
    ext i
    have coord := h i
    by_cases hi : i ∈ H <;> simpa [hits,hi] using coord
  · intro eq i
    have hi : i ∈ H ↔ σ i ∈ C i := by rw [← eq];simp [hits]
    by_cases mem : i ∈ H <;> simp [mem,← hi]

private theorem pattern_card {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
    (C : ι → Finset Ω) (H : Finset ι) (m : ℕ) (size : ∀ i, (C i).card=m) :
    (pattern C H).card=m^H.card*(Fintype.card Ω-m)^(Fintype.card ι-H.card) := by
  rw [pattern,Fintype.card_piFinset]
  rw [← prod_filter_mul_prod_filter_not (s:=univ) (p:=fun i => i ∈ H)]
  have left : univ.filter (fun i => i ∈ H)=H := by ext; simp
  have right : univ.filter (fun i => i ∉ H)=Hᶜ := by ext; simp
  rw [left,right]
  have a : ∀ i ∈ H, (if i ∈ H then C i else (C i)ᶜ).card=m := by
    intro i hi
    simp [hi,size]
  have b : ∀ i ∈ Hᶜ, (if i ∈ H then C i else (C i)ᶜ).card=Fintype.card Ω-m := by
    intro i hi
    simp [mem_compl.mp hi,size,card_compl]
  rw [prod_congr rfl a,prod_congr rfl b]
  simp [card_compl]

/-- Exact binomial tail multiplied by the number of all shift arrays. -/
def badCount (r t m : ℕ) (bad : Finset ℕ) :=
  ∑ j ∈ (range (r+1)).filter (fun j => j ∈ bad), r.choose j*m^j*(t-m)^(r-j)

theorem one_test {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
    (C : ι → Finset Ω) (m : ℕ) (size : ∀ i, (C i).card=m) (bad : Finset ℕ) :
    (univ.filter (fun σ : ι → Ω => (hits C σ).card ∈ bad)).card =
      badCount (Fintype.card ι) (Fintype.card Ω) m bad := by
  classical
  let r := Fintype.card ι
  let t := Fintype.card Ω
  let counts := (range (r+1)).filter (fun j => j ∈ bad)
  let patterns (j : ℕ) := (univ : Finset ι).powersetCard j
  let layer (j : ℕ) := (patterns j).biUnion (pattern C)
  have sizeLayer (j : ℕ) : (layer j).card=r.choose j*m^j*(t-m)^(r-j) := by
    have disj : (↑(patterns j) : Set (Finset ι)).PairwiseDisjoint (pattern C) := by
      intro A _ B _ ne
      apply disjoint_left.mpr
      intro σ ha hb
      exact ne (((mem_pattern C A σ).mp ha).symm.trans ((mem_pattern C B σ).mp hb))
    change ((patterns j).biUnion (pattern C)).card=_
    rw [card_biUnion disj]
    have each (H : Finset ι) (hH : H ∈ patterns j) :
        (pattern C H).card=m^j*(t-m)^(r-j) := by
      rw [pattern_card _ _ _ size,(mem_powersetCard.mp hH).2]
    rw [sum_congr rfl each]
    simp [patterns,t,r,Nat.mul_assoc]
  have memL (j : ℕ) (σ : ι → Ω) : σ ∈ layer j ↔ (hits C σ).card=j := by
    constructor
    · intro h
      obtain ⟨H,hH,hσ⟩ := mem_biUnion.mp h
      rw [(mem_pattern C H σ).mp hσ]
      exact (mem_powersetCard.mp hH).2
    · intro h
      exact mem_biUnion.mpr ⟨_,mem_powersetCard.mpr ⟨subset_univ _,h⟩,(mem_pattern _ _ _).mpr rfl⟩
  have eq : univ.filter (fun σ : ι → Ω => (hits C σ).card ∈ bad) = counts.biUnion layer := by
    ext σ
    simp only [mem_filter,mem_univ,true_and,mem_biUnion,memL]
    constructor
    · intro h
      exact ⟨_,mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (card_le_univ _)),h⟩,rfl⟩
    · rintro ⟨j,hj,e⟩
      exact e ▸ (mem_filter.mp hj).2
  have disj : (↑counts : Set ℕ).PairwiseDisjoint layer := by
    intro j _ l _ ne
    exact disjoint_left.mpr (fun σ hj hl => ne (((memL j σ).mp hj).symm.trans ((memL l σ).mp hl)))
  rw [eq,card_biUnion disj]
  exact sum_congr rfl (fun j _ => sizeLayer j)

/-- One assignment passes all tests, for an arbitrary prescribed set
    of forbidden counts and precisely the ordinary binomial union bound. -/
theorem select {ι Ω τ : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
    (F : Finset τ) (C : τ → ι → Finset Ω) (m : ℕ) (bad : Finset ℕ)
    (size : ∀ f ∈ F, ∀ i, (C f i).card=m)
    (budget : F.card*badCount (Fintype.card ι) (Fintype.card Ω) m bad <
      (Fintype.card Ω)^(Fintype.card ι)) :
    ∃ σ : ι → Ω, ∀ f ∈ F, (hits (C f) σ).card ∉ bad := by
  classical
  let fail (f : τ) := univ.filter (fun σ : ι → Ω => (hits (C f) σ).card ∈ bad)
  by_contra! h
  have sub : (univ : Finset (ι → Ω)) ⊆ F.biUnion fail := by
    intro σ _
    obtain ⟨f,hf,b⟩ := h σ
    exact mem_biUnion.mpr ⟨f,hf,mem_filter.mpr ⟨mem_univ _,b⟩⟩
  have u := (card_le_card sub).trans card_biUnion_le
  have each (f : τ) (hf : f ∈ F) := one_test (C f) m (size f hf) bad
  rw [sum_congr rfl each] at u
  simp only [card_univ,Fintype.card_fun,sum_const,nsmul_eq_mul] at u
  exact (not_le_of_gt budget) u

#print axioms one_test
#print axioms select
end Erdos142RowSelection
