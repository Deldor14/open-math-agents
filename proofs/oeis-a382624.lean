import OMAStatements.S_oeis_a382624
import Mathlib

open OMA.S_oeis_a382624
namespace Deldor14.Greedy382624

def rep : ℕ → ℕ
  | 0 => 9
  | j+1 => 9+10*rep j

theorem repMono : StrictMono rep := by
  apply strictMono_nat_of_lt_succ
  intro k
  change rep k < 9+10*rep k
  omega

theorem digits (j : ℕ) : Nat.digits 10 (rep j)=List.replicate (j+1) 9 := by
  induction j with
  | zero => decide +kernel
  | succ j ih =>
    rw [rep,Nat.digits_add _ (by decide) _ _ (by decide) (Or.inl (by decide)),ih]
    rfl

theorem allowed (j : ℕ) : admissible (rep j) := by
  unfold admissible
  rw [digits,List.reverse_replicate]
  have ch := List.isChain_replicate_of_rel (j+1) (show digitStep 9 9 by simp [digitStep])
  have p : 0<rep j := by cases j <;> simp [rep]
  exact ⟨p,ch⟩

theorem repFirst (j : ℕ) : firstDigit (rep j)=9 := by rw [firstDigit,digits,List.reverse_replicate,List.replicate_succ]; rfl
theorem repLast (j : ℕ) : lastDigit (rep j)=9 := by simp [lastDigit,digits,List.replicate_succ]

theorem canEnter (x : ℕ) (_ : admissible x) (j : ℕ) : follows x (rep j) := by
  simp [follows,repFirst,digitStep]

theorem canLeave (j x : ℕ) (hx : admissible x) : follows (rep j) x := by
  rw [follows,repLast]
  intro he
  have cap : firstDigit x<10 := by
    unfold firstDigit
    cases h : (Nat.digits 10 x).reverse with
    | nil => decide
    | cons a t =>
      have mem : a ∈ (Nat.digits 10 x).reverse := by simp [h]
      exact Nat.digits_lt_base (by decide) (List.mem_reverse.mp mem)
  omega

theorem fresh (used : Finset ℕ) : ∃ j, rep j ∉ used := by
  by_contra! h
  have sub : Set.range rep ⊆ (used : Set ℕ) := Set.range_subset_iff.mpr h
  exact (Set.infinite_range_of_injective repMono.injective) (used.finite_toSet.subset sub)

theorem valid (n : ℕ) : admissible (state n).2 := by
  induction n with
  | zero => exact allowed 0
  | succ n ih =>
    change admissible (next (state n).1 (state n).2)
    obtain ⟨j,hj⟩ := fresh (state n).1
    exact (Nat.sInf_mem (show {m : ℕ | admissible m ∧ m ∉ (state n).1 ∧ follows (state n).2 m}.Nonempty
      from ⟨rep j,allowed j,hj,canEnter _ ih j⟩)).1

theorem chosen (n : ℕ) : admissible (a n) ∧ a n ∉ (state n).1 ∧ follows (state n).2 (a n) := by
  obtain ⟨j,hj⟩ := fresh (state n).1
  exact Nat.sInf_mem (show {m : ℕ | admissible m ∧ m ∉ (state n).1 ∧ follows (state n).2 m}.Nonempty
    from ⟨rep j,allowed j,hj,canEnter _ (valid n) j⟩)

theorem used (n x : ℕ) : x ∈ (state n).1 ↔ ∃ i<n, a i=x := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    change x ∈ insert (a n) (state n).1 ↔ _
    rw [Finset.mem_insert,ih]
    constructor
    · rintro (h | ⟨i,hi,e⟩)
      · exact ⟨n,by omega,h.symm⟩
      · exact ⟨i,by omega,e⟩
    · rintro ⟨i,hi,e⟩
      by_cases h : i=n
      · exact Or.inl (h ▸ e.symm)
      · exact Or.inr ⟨i,by omega,e⟩

theorem inj : Function.Injective a := by
  have diff {i j : ℕ} (lt : i<j) : a i ≠ a j := fun e =>
    (chosen j).2.1 ((used j _).mpr ⟨i,lt,e⟩)
  intro i j eq
  by_contra! ne
  rcases lt_or_gt_of_ne ne with h | h
  · exact diff h eq
  · exact diff h eq.symm

theorem bound (m : ℕ) (hm : admissible m) (miss : ¬∃ i,a i=m) (n : ℕ)
    (follow : follows (state n).2 m) : a n ≤ m := by
  apply Nat.sInf_le
  exact ⟨hm,fun h => by obtain ⟨i,_,eq⟩ := (used n m).mp h; exact miss ⟨i,eq⟩,follow⟩

theorem finiteRange (f : ℕ → ℕ) (hf : Function.Injective f) (m : ℕ) (cap : ∀ i,f i ≤ m) : False := by
  exact (Set.infinite_range_of_injective hf) ((Set.finite_Iic m).subset (Set.range_subset_iff.mpr cap))

theorem hitsRep (j : ℕ) : ∃ i,a i=rep j := by
  by_contra miss
  exact finiteRange a inj (rep j) (fun n => bound _ (allowed j) miss n (canEnter _ (valid n) j))

theorem hits (m : ℕ) (hm : admissible m) : ∃ n,a n=m := by
  choose idx hidx using hitsRep
  have ii : Function.Injective idx := fun x y h =>
    repMono.injective ((hidx x).symm.trans ((congrArg a h).trans (hidx y)))
  by_contra miss
  apply finiteRange (fun j => a (idx j+1)) (inj.comp (Nat.succ_injective.comp ii)) m
  intro j
  apply bound m hm miss
  change follows (a (idx j)) m
  rw [hidx]
  exact canLeave j m hm

end Deldor14.Greedy382624
open Deldor14.Greedy382624

theorem OMA.solution : type_of% @OMA.S_oeis_a382624.main := by
  refine ⟨inj,fun m => ⟨?_,hits m⟩⟩
  rintro ⟨n,rfl⟩
  exact (chosen n).1
