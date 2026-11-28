import RothHalfScale
import RothGrowth
import RothHeight

open Finset
namespace Erdos142HalfScale
open Erdos142InducedTriples Erdos142DyadicClusters Erdos142ExactDefects

/-- Cost of nonoptimality and of the two covers, before any boundary losses. -/
def cost (n : ℕ) (A C D : Finset ℕ) := rothNumberNat n-A.card+(C ∪ D).card

private theorem bounds (A C D : Finset ℕ) (n t : ℕ) (ht : 0<t) (fit : A ⊆ range n)
    (free : ThreeAPFree (↑A : Set ℕ)) (hc : Covers A C t) (hd : Covers A D (2*t)) :
    2*rothNumberNat n ≤ rothNumberNat (2*n)+8*cost n A C D+7*rothNumberNat (2*t) ∧
    5*rothNumberNat n ≤ 8*rothNumberNat ((n+1)/2)+20*cost n A C D+23*rothNumberNat (2*t) := by
  let B := A \ (C ∪ D)
  have sub : B ⊆ A := sdiff_subset
  have exc {x} (hx : x ∈ B) : x ∉ C ∧ x ∉ D := by simpa using (mem_sdiff.mp hx).2
  have weak : Weak t B := by
    intro x hx y hy z hz eq
    by_contra! ne
    obtain ⟨xy,yz,xz⟩ := ne
    have w0 : x+z≠y+y := fun e => xz (threeAPFree_iff_eq_right.mp free (sub hx) (sub hy) (sub hz) e)
    have w1 : |(x:ℤ)+z-2*y|≠(t:ℤ) := by
      intro e
      rcases hc x (sub hx) y (sub hy) z (sub hz) xy yz xz e with h|h|h
      · exact (exc hx).1 h
      · exact (exc hy).1 h
      · exact (exc hz).1 h
    have w2 : |(x:ℤ)+z-2*y|≠↑(2*t) := by
      intro e
      rcases hd x (sub hx) y (sub hy) z (sub hz) xy yz xz e with h|h|h
      · exact (exc hx).2 h
      · exact (exc hy).2 h
      · exact (exc hz).2 h
    push_cast at w2
    rw [abs_eq_max_neg] at w1 w2
    omega
  have loc := sub.trans fit
  have cut : A.card ≤ B.card+(C ∪ D).card := by
    calc
      _ ≤ (B ∪ (C ∪ D)).card := card_le_card (by
        intro x hx; by_cases h : x ∈ C ∪ D
        · exact mem_union_right _ h
        · exact mem_union_left _ (mem_sdiff.mpr ⟨hx,h⟩))
      _ ≤ _ := card_union_le _ _
  have one := integer_gain B n t ht loc weak
  have up := four_per_pair ht loc weak
  have down := half_per_pair ht loc weak
  have nt := rothNumberNat_add_le n t
  have tail := rothNumberNat.monotone (show t≤2*t by omega)
  have ntwo := rothNumberNat_add_le (2*n) (2*t)
  have nhalf := rothNumberNat_add_le ((n+1)/2) (2*t)
  dsimp only [cost]
  constructor <;> omega

/-- Every two adjacent lengths satisfy a joint defect-cover inequality,
    for independently chosen steps, sets and covers. -/
theorem adjacent (A C D A' C' D' : Finset ℕ) (n t s : ℕ) (ht : 0<t) (hs : 0<s)
    (fit : A ⊆ range n) (fit' : A' ⊆ range (2*n))
    (free : ThreeAPFree (↑A : Set ℕ)) (free' : ThreeAPFree (↑A' : Set ℕ))
    (hc : Covers A C t) (hd : Covers A D (2*t))
    (hc' : Covers A' C' s) (hd' : Covers A' D' (2*s)) :
    2*rothNumberNat n ≤ 40*cost n A C D+20*cost (2*n) A' C' D'+
      35*rothNumberNat (2*t)+23*rothNumberNat (2*s) := by
  have first := (bounds A C D n t ht fit free hc hd).1
  have second := (bounds A' C' D' (2*n) s hs fit' free' hc' hd').2
  rw [show (2*n+1)/2=n by omega] at second
  omega

private theorem ternary (d : ℕ) : 2^d≤rothNumberNat (3^d) := by
  induction d with
  | zero =>
    simp only [pow_zero]
    have f : ThreeAPFree (↑({0} : Finset ℕ) : Set ℕ) := by simp
    exact f.le_rothNumberNat {0} (by simp) (by simp)
  | succ d ih =>
    have pos : 0<3^d := pow_pos (by decide) _
    have h := Erdos142Growth.glue (3^d) (3^d) (3^(d+1)) pos le_rfl (by rw [pow_succ]; omega)
    rw [pow_succ]
    omega

private theorem tail_bound {n t : ℕ} (h : 26244*t≤n) :
    256*rothNumberNat (2*t)≤rothNumberNat n := by
  have d := Erdos142Height.digit_product (2*t) (3^8)
  have b := Nat.mul_le_mul_left (rothNumberNat (2*t)) (ternary 8)
  norm_num at d b
  have m := rothNumberNat.monotone h
  rw [show 2*(2*t)*6561=26244*t by ring] at d
  omega

def good (n : ℕ) := ∀ (A C D : Finset ℕ) (t : ℕ), 0<t → 26244*t≤n →
    A ⊆ range n → ThreeAPFree (↑A : Set ℕ) → Covers A C t → Covers A D (2*t) →
    rothNumberNat n < 50*cost n A C D

/-- At one of exactly two specified lengths the conclusion holds simultaneously
    for all free sets, both covers and all steps through a fixed fraction. -/
theorem one_of_two (n : ℕ) (positive : 0<rothNumberNat n) : good n ∨ good (2*n) := by
  by_contra! h
  obtain ⟨h1,h2⟩ := h
  unfold good at h1 h2
  push Not at h1 h2
  obtain ⟨A,C,D,t,ht,bt,fit,free,hc,hd,small⟩ := h1
  obtain ⟨A',C',D',s,hs,bs,fit',free',hc',hd',small'⟩ := h2
  have both := adjacent A C D A' C' D' n t s ht hs fit fit' free free' hc hd hc' hd'
  have b1 := tail_bound bt
  have b2 := tail_bound bs
  have cap := rothNumberNat_add_le n n
  rw [← two_mul] at cap
  omega

#print axioms adjacent
#print axioms one_of_two
end Erdos142HalfScale
