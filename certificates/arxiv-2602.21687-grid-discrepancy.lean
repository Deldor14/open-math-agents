import Mathlib

/-!
# Perpetually Fair Assignments Via Balanced Sequences of Permutations

Source: https://arxiv.org/abs/2602.21687v3 (Adams and Segal-Halevi), Section 7, Open Question 1:
"Is there, for every n ≥ 1, a 2-balanced permutation sequence?"
Credit: @tatashbar

Model (Section 2). There are `n` items `1, …, n` (item `1` is the best) and `n` players. On each of
the days `1, …, n` an assignment, a bijection from items to players, is used. A permutation sequence
is this list of `n` assignments. The source does not require it to be a latin square.

`Z_i^t` is the multiset of items that player `i` holds after day `t`, and `Z_i^t[j]` is its `j`-th
smallest label. For an integer `c ≥ 1`, the sequence is `c`-balanced (Section 7, condition (3)) if
`Z_i^t[j] ≤ ⌊(j + c - 1) n / t + 1⌋` for all players `i`, all days `t ∈ [n]` and all `j ∈ [t]`.

Here `Z_i^t[j] ≤ B` is written as: at least `j` of the first `t` items of player `i` have label at
most `B`. This is the same condition, because `Z_i^t` has exactly `t` elements.

Known from the source: the stronger conditions with bound `⌈j n / t⌉` (fully balanced) and
`⌊j n / t + 1⌋` (weakly fully balanced, the case `c = 1`) hold for some sequence when `n ≤ 11` and
`n ≤ 12`, and for no sequence when `n > 61` and `n > 108`. The case `c = 2` is open in the source.

Note from the contributor, not from the source and not formalised: an argument through Halász's
L1 lower bound for the discrepancy of point sets in the square gives `c ≥ κ √(log n) - O(1)` for
every `c`-balanced sequence, so `main` would be false for all sufficiently large `n`. The argument
gives no explicit `n`. The statement below is the question exactly as the source asks it.
-/

namespace OMA.S_arxiv_2602_21687

/-- The label (from `1` to `n`) of the item that player `i` receives on day `d`, where `s d` maps
each item to the player who receives it on day `d`. -/
def item {n : ℕ} (s : Fin n → Equiv.Perm (Fin n)) (i d : Fin n) : ℕ :=
  ((s d).symm i).val + 1

/-- The number of the first `t` days on which player `i` receives an item with label at most `B`. -/
def countUpTo {n : ℕ} (s : Fin n → Equiv.Perm (Fin n)) (i : Fin n) (t B : ℕ) : ℕ :=
  (Finset.univ.filter fun d : Fin n => d.val < t ∧ item s i d ≤ B).card

/-- Condition (3) of the source: `Z_i^t[j] ≤ ⌊(j + c - 1) n / t + 1⌋` for all `i`, all `t ∈ [n]`
and all `j ∈ [t]`. -/
def IsBalanced {n : ℕ} (c : ℕ) (s : Fin n → Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, ∀ t j : ℕ, 1 ≤ j → j ≤ t → t ≤ n →
    j ≤ countUpTo s i t ((j + c - 1) * n / t + 1)

end OMA.S_arxiv_2602_21687
namespace Deldor14.BalancedDiscrepancy
open Finset OMA.S_arxiv_2602_21687
private theorem prefix_card (n k : ℕ) (hk : k≤n) :
    (univ.filter (fun i : Fin n => i.val < k)).card=k := by
  calc
    _ = (univ : Finset (Fin k)).card := by
      apply card_bij (fun a h => (⟨a.val,(mem_filter.mp h).2⟩ : Fin k))
      · simp
      · intro a ha b hb eq
        exact Fin.ext (congrArg (fun z : Fin k => z.val) eq)
      · intro b _
        refine ⟨⟨b.val,lt_of_lt_of_le b.isLt hk⟩,mem_filter.mpr ⟨mem_univ _,b.isLt⟩,rfl⟩
    _ = _ := by simp

/-- On any t by k prefix, a 2-balanced sequence leaves each player's
count at most two below the ideal share, after dividing both sides by n. -/
theorem lower {n : ℕ} {s : Fin n → Equiv.Perm (Fin n)} (bal : IsBalanced 2 s)
    (i : Fin n) (t k : ℕ) (ht : t≤n) (hk : k≤n) :
    k*t ≤ (countUpTo s i t k+2)*n := by
  let q := countUpTo s i t k
  change k*t ≤ (q+2)*n
  by_cases small : q<t
  · have h := bal i t (q+1) (by omega) (by omega) ht
    have hc : ¬ ((q+1+2-1)*n/t+1≤k) := by
      intro bound
      have sub : countUpTo s i t ((q+1+2-1)*n/t+1) ≤ q := by
        apply card_le_card
        intro d hd
        obtain ⟨_,day,rank⟩ := mem_filter.mp hd
        exact mem_filter.mpr ⟨mem_univ _,day,rank.trans bound⟩
      omega
    have div : k≤(q+2)*n/t := by
      rw [show q+1+2-1=q+2 by omega] at hc
      omega
    exact (Nat.le_div_iff_mul_le (by omega)).mp div
  · calc
      k*t ≤ n*q := Nat.mul_le_mul hk (by omega)
      _ ≤ _ := by rw [mul_comm n q];gcongr;omega

private theorem indicators (n k : ℕ) (hk : k≤n) :
    (∑ i : Fin n, if i.val<k then (1:ℕ) else 0)=k := by
  rw [←sum_filter,sum_const,prefix_card n k hk]
  simp

/-- Each day's assignment is a permutation, so the total across all players
in a t by k prefix is exactly the area of that rectangle. -/
theorem conserve {n : ℕ} (s : Fin n → Equiv.Perm (Fin n)) (t k : ℕ)
    (ht : t≤n) (hk : k≤n) : (∑ i, countUpTo s i t k)=t*k := by
  calc
    _ = ∑ i : Fin n, ∑ d : Fin n, if d.val<t then
         (if ((s d).symm i).val<k then (1:ℕ) else 0) else 0 := by
      apply sum_congr rfl
      intro i _
      unfold countUpTo
      rw [card_eq_sum_ones,sum_filter]
      apply sum_congr rfl
      intro d _
      unfold item
      split_ifs <;> simp_all <;> omega
    _ = ∑ d : Fin n, if d.val<t then k else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      by_cases h : d.val<t
      · simp only [if_pos h]
        exact ((s d).symm.sum_comp (fun j : Fin n => if j.val<k then (1:ℕ) else 0)).trans (indicators n k hk)
      · simp [h]
    _ = _ := by rw [←sum_filter,sum_const,prefix_card n t ht];simp

def error {n : ℕ} (s : Fin n → Equiv.Perm (Fin n)) (i : Fin n) (t k : ℕ) : ℤ :=
  (n:ℤ)*countUpTo s i t k - (t:ℤ)*k

theorem mean_absolute_bound {n : ℕ} {s : Fin n → Equiv.Perm (Fin n)} (bal : IsBalanced 2 s)
    (t k : ℕ) (ht : t≤n) (hk : k≤n) : (∑ i, |error s i t k|) ≤ 4*(n:ℤ)^2 := by
  have cons : (∑ i : Fin n,(countUpTo s i t k : ℤ))=(t:ℤ)*k := by
    exact_mod_cast conserve s t k ht hk
  have zero : (∑ i : Fin n,error s i t k)=0 := by
    simp only [error,sum_sub_distrib,←mul_sum,cons,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  calc
    _ ≤ ∑ i : Fin n,(error s i t k+4*(n:ℤ)) := by
      apply sum_le_sum
      intro i _
      have h : (k:ℤ)*t ≤ ((countUpTo s i t k:ℤ)+2)*n := by
        exact_mod_cast lower bal i t k ht hk
      rw [abs_le]
      unfold error
      constructor <;> nlinarith
    _ = _ := by rw [sum_add_distrib,zero]; simp;ring
#print axioms lower
#print axioms conserve
#print axioms mean_absolute_bound
end Deldor14.BalancedDiscrepancy

namespace Deldor14.BalancedDiscrepancy
open Finset OMA.S_arxiv_2602_21687
/-- Scaled, unnormalized total absolute discrepancy of the graph of a single
player's rank sequence, sampled at the n² grid corners. -/
def total {n : ℕ} (f : Fin n → Fin n) : ℤ :=
  ∑ t : Fin n, ∑ k : Fin n,
    |(n:ℤ)*(univ.filter (fun d : Fin n => d.val<t.val ∧ (f d).val<k.val)).card -
      (t.val:ℤ)*k.val|
private theorem individual {n : ℕ} (s : Fin n → Equiv.Perm (Fin n)) (i : Fin n) :
    total (fun d => (s d).symm i) = ∑ t : Fin n, ∑ k : Fin n, |error s i t.val k.val| := by
  simp only [total,error,countUpTo,item,Nat.add_one_le_iff]
theorem some_player {n : ℕ} (hn : 0<n) {s : Fin n → Equiv.Perm (Fin n)} (bal : IsBalanced 2 s) :
    ∃ i : Fin n, total (fun d => (s d).symm i) ≤ 4*(n:ℤ)^3 := by
  have all : (∑ i : Fin n,total (fun d => (s d).symm i)) ≤ (n:ℤ)*(4*(n:ℤ)^3) := by
    simp_rw [individual s]
    calc
      _ = ∑ t : Fin n, ∑ k : Fin n, ∑ i : Fin n, |error s i t.val k.val| := by
        rw [sum_comm]
        apply sum_congr rfl
        intro t _
        rw [sum_comm]
      _ ≤ ∑ _t : Fin n, ∑ _k : Fin n, 4*(n:ℤ)^2 := by
        apply sum_le_sum
        intro t _
        apply sum_le_sum
        intro k _
        exact mean_absolute_bound bal _ _ t.isLt.le k.isLt.le
      _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul];ring
  by_contra! bad
  have ne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,mem_univ _⟩
  have excess := Finset.sum_lt_sum_of_nonempty ne (fun i _ => bad i)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at excess
  omega
/-- A universal lower bound for all rank sequences at one grid size,
with the displayed normalization, would disprove universal 2-balance. -/
theorem discrepancy_obstruction
    (obstruction : ∃ n : ℕ, 0<n ∧ ∀ f : Fin n → Fin n, 4*(n:ℤ)^3 < total f) :
    ¬(∀ n : ℕ, 1≤n → ∃ s : Fin n → Equiv.Perm (Fin n), IsBalanced 2 s) := by
  obtain ⟨n,hn,lower⟩ := obstruction
  intro claim
  obtain ⟨s,hs⟩ := claim n hn
  obtain ⟨i,hi⟩ := some_player hn hs
  exact (not_lt_of_ge hi) (lower _)
#print axioms some_player
#print axioms discrepancy_obstruction
end Deldor14.BalancedDiscrepancy
