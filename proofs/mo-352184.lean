import OMAStatements.S_mo_352184
import Mathlib

open OMA.S_mo_352184 Finset
namespace Deldor14.Tournament

abbrev V := Fin 16
private def rows : V → ℕ := ![14,28,104,896,64525,15451,31771,1911,3703,7287,63503,61583,57743,50063,33711,1007]
private def wins (i j : V) : Bool := (rows i).testBit j.val
private def G : Digraph V := ⟨fun i j => wins i j=true⟩
private theorem tour : IsTournament G := by
  change (∀ i : V,wins i i≠true) ∧ (∀ i j : V,i≠j → (wins i j=true ↔ wins j i≠true))
  decide +kernel

private theorem scoreG (i : V) : score G i=3 ∨ score G i=9 := by
  have eq : score G i=(univ.filter (fun j => wins i j=true)).card := by
    simp [score,G,Set.ncard_eq_toFinset_card']
  rw [eq]
  clear eq
  revert i; decide +kernel

private def count (f : V → V) (i : V) : ℕ :=
  (univ.filter (fun u => (u < i ∧ i≤f u) ∨ (i < u ∧ f i < u))).card

private theorem countFair (T : Digraph V) (hT : IsTournament T) (f : V → V)
    (cuts : ∀ i k,i < k → (T.Adj i k ↔ f i < k)) (i : V) : score T i=count f i := by
  classical
  have edge (k : V) : T.Adj i k ↔ (k < i ∧ i≤f k) ∨ (i < k ∧ f i < k) := by
    rcases lt_trichotomy k i with h|e|h
    · rw [hT.2 i k h.ne',cuts k i h]
      simp [h,not_lt_of_ge h.le]
    · subst k; simp [hT.1]
    · rw [cuts i k h]; simp [h,not_lt_of_ge h.le]
  simp only [score,count,Set.ncard_eq_toFinset_card']
  congr 1; ext u; simp [edge]

/-- Fill the unknown thresholds from left to right, discarding a prefix once
the current score is neither 3 nor 9. The score reads only thresholds up to i. -/
private def possible : ℕ → ℕ → (V → V) → Bool
  | 0,_,_ => true
  | k+1,i,f =>
    let v : V := Fin.ofNat 16 i
    decide (∃ j : V, v≤j ∧
      let g := Function.update f v j
      (count g v=3 ∨ count g v=9) ∧ possible k (i+1) g=true)

private theorem follows (t : V → V) (valid : ∀ i,i≤t i) (scores : ∀ i,count t i=3 ∨ count t i=9)
    (k i : ℕ) (hi : i+k=16) (f : V → V) (agree : ∀ u : V,u.val < i → f u=t u) :
    possible k i f=true := by
  induction k generalizing i f with
  | zero => rfl
  | succ k ih =>
    let v : V := Fin.ofNat 16 i
    have val : v.val=i := Nat.mod_eq_of_lt (by omega)
    let g := Function.update f v (t v)
    have extended (u : V) (h : u.val < i+1) : g u=t u := by
      by_cases e : u=v
      · subst u; simp [g]
      · change Function.update f v (t v) u=t u
        rw [Function.update_of_ne e]
        apply agree; have hne : u.val≠v.val := fun q => e (Fin.ext q)
        omega
    have same : count g v=count t v := by
      unfold count; congr 1; ext u
      simp only [mem_filter,mem_univ,true_and]
      rw [extended v (by omega)]
      by_cases hu : u < v
      · rw [extended u (by change u.val < v.val at hu; omega)]
      · simp [hu]
    change decide (∃ j : V,v≤j ∧ _) = true
    apply decide_eq_true
    exact ⟨t v,valid v,by simpa only [← same] using scores v,ih _ (by omega) g extended⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem impossible : possible 16 0 (fun _ => 0)=false := by decide +kernel

theorem result : ¬ (type_of% @OMA.S_mo_352184.main) := by
  rintro all
  obtain ⟨T,hT,fair,perm,matchScore⟩ := all 16 G tour
  choose t lo cut using fair
  have good (i : V) : count t i=3 ∨ count t i=9 := by
    rw [← countFair T hT t cut i]
    obtain ⟨j,rfl⟩ := perm.surjective i
    rw [← matchScore j]; exact scoreG j
  have ok := follows t lo good 16 0 rfl (fun _ => 0) (fun _ h => by omega)
  rw [impossible] at ok
  contradiction

end Deldor14.Tournament
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_352184.main) := Deldor14.Tournament.result
