import CompositionClock

/-! Local effect of replacing just the m-th weight of a composition clock. -/

namespace Erdos142BurstClock
open Erdos142CompositionClock

theorem clock_mono (b : ℕ → ℕ) : Monotone (u b) := by
  intro i j le
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le le
  exact (Nat.le_add_right _ _).trans (superadditive b i k)

private theorem sum_bounds_part {L : List ℕ} {t : ℕ} (ht : t ∈ L) : t ≤ L.sum := by
  obtain ⟨left,right,rfl⟩ := List.append_of_mem ht
  simp only [List.sum_append,List.sum_cons]
  omega

private theorem maps_agree {b b' : ℕ → ℕ} {m : ℕ}
    (same : ∀ t, t ≠ m → b' t=b t) {L : List ℕ} (skip : m ∉ L) :
    L.map b' = L.map b := by
  apply List.map_congr_left
  intro t ht
  exact same t (fun eq => skip (eq ▸ ht))

/-- No positive composition of a total below m uses the changed weight. -/
theorem unchanged_below {b b' : ℕ → ℕ} {m s : ℕ}
    (same : ∀ t, t ≠ m → b' t=b t) (sm : s < m) : u b' s = u b s := by
  have eq (c : Composition s) : weight b' c=weight b c := by
    unfold weight
    rw [maps_agree same (L := c.blocks) (by
      intro hm
      have part := sum_bounds_part hm
      rw [c.blocks_sum] at part
      omega)]
  obtain ⟨a,ha⟩ := winner b' s
  obtain ⟨d,hd⟩ := winner b s
  exact le_antisymm (ha ▸ eq a ▸ le_u b a) (hd ▸ (eq d).symm ▸ le_u b' d)

/-- On [m,m+h], one occurrence of m attains the maximum. Ties with
compositions omitting m are permitted when the new weight equals the bound. -/
theorem burst_value {b b' : ℕ → ℕ} {m h s K : ℕ} (hm : h < m) (hs : s ≤ h)
    (same : ∀ t, t ≠ m → b' t=b t) (hit : b' m=K)
    (high : u b (m+h) ≤ K) : u b' (m+s) = K+u b s := by
  have small := unchanged_below same (hs.trans_lt hm)
  have lower := positive_step b' s m (by omega)
  rw [small,hit,Nat.add_comm s m,Nat.add_comm (u b s)] at lower
  apply le_antisymm _ lower
  obtain ⟨c,win⟩ := winner b' (m+s)
  by_cases used : m ∈ c.blocks
  · let rest := c.blocks.erase m
    have perm : c.blocks.Perm (m::rest) := List.perm_cons_erase used
    have mass : rest.sum=s := by
      have e := perm.sum_eq
      rw [c.blocks_sum,List.sum_cons] at e
      omega
    let d : Composition s := ⟨rest,fun ht => c.blocks_pos (List.mem_of_mem_erase ht),mass⟩
    have price := (perm.map b').sum_eq
    simp only [List.map_cons,List.sum_cons] at price
    change weight b' c=b' m+weight b' d at price
    have best := le_u b' d
    rw [small] at best
    rw [← win,price,hit]
    exact Nat.add_le_add_left best K
  · have eq : weight b' c=weight b c := by
      unfold weight
      rw [maps_agree same used]
    have upper := (le_u b c).trans (clock_mono b (Nat.add_le_add_left hs m))
    rw [← win,eq]
    exact (upper.trans high).trans (Nat.le_add_right _ _)

#print axioms unchanged_below
#print axioms burst_value
end Erdos142BurstClock
