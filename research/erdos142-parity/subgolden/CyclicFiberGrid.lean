import ExactInterpolation

/-! The residue-fibre construction and interpolation originate in Left to Solve
notes #181029 and #181117 by @pwamsley2015. Here we average every cyclic
translate and keep the exact adjacent-integer weights on any rational grid. -/

namespace Erdos142CyclicFiber
open Finset Erdos142GridInterpolation

private theorem packed {L : ℕ} [NeZero L] (D : Finset (Fin L))
    (free : ThreeAPFree (D : Set (Fin L))) (q d : ℕ) (t : Fin L) :
    ∑ x ∈ D, rothNumberNat (if (x+t).val < d then q+1 else q)
      ≤ rothNumberNat (L*q+d) := by
  classical
  have hL : 0<L := Nat.pos_of_ne_zero (NeZero.ne L)
  let size (x : Fin L) := if (x+t).val < d then q+1 else q
  choose H hsub hcard hfree using fun x : Fin L => rothNumberNat_spec (size x)
  let word (x : Fin L) (u : ℕ) := (x+t).val + L*u
  let T (x : Fin L) := (H x).image (word x)
  let U := D.biUnion T
  let red (a : ℕ) : Fin L := Fin.ofNat L a
  have red_add (a b : ℕ) : red (a+b)=red a+red b := Fin.ext (Nat.add_mod a b L)
  have residue (x : Fin L) (u : ℕ) : red (word x u) = x+t := by
    apply Fin.ext
    change ((x+t).val+L*u)%L=(x+t).val
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (x+t).isLt]
  have disj : (D : Set (Fin L)).PairwiseDisjoint T := by
    intro x _ y _ hne
    apply Finset.disjoint_left.mpr
    intro z hzx hzy
    obtain ⟨u,_,hu⟩ := mem_image.mp hzx
    obtain ⟨v,_,hv⟩ := mem_image.mp hzy
    exact hne (add_right_cancel ((residue x u).symm.trans
      ((congrArg red (hu.trans hv.symm)).trans (residue y v))))
  have Ufree : ThreeAPFree (U : Set ℕ) := by
    intro X hX Y hY Z hZ eq
    obtain ⟨x,hx,hX⟩ := mem_biUnion.mp hX
    obtain ⟨y,hy,hY⟩ := mem_biUnion.mp hY
    obtain ⟨z,hz,hZ⟩ := mem_biUnion.mp hZ
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hX
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hY
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hZ
    have r := congrArg red eq
    simp only [red_add, residue] at r
    have step : x+z=y+y := by
      apply add_right_cancel (b:=t+t)
      simpa only [add_add_add_comm x z t t,add_add_add_comm y y t t] using r
    have xy := free hx hy hz step
    have zy := free hz hy hx ((add_comm z x).trans step)
    subst y
    subst z
    have reord : (x+t).val+(x+t).val + L*(u+w) =
        (x+t).val+(x+t).val + L*(v+v) := by
      unfold word at eq
      simp only [Nat.mul_add]
      omega
    have uv := hfree x hu hv hw (Nat.eq_of_mul_eq_mul_left hL (Nat.add_left_cancel reord))
    rw [uv]
  have bound {z : ℕ} (hz : z ∈ U) : z < L*q+d := by
    obtain ⟨x,_,hx⟩ := mem_biUnion.mp hz
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
    have h := Finset.mem_range.mp (hsub x hu)
    unfold size at h
    dsimp [word]
    split at h <;> rename_i hres
    · have m := Nat.mul_le_mul_left L (by omega : u ≤ q)
      omega
    · have m := Nat.mul_le_mul_left L (by omega : u+1 ≤ q)
      rw [Nat.mul_succ] at m
      have := (x+t).isLt
      omega
  have out := Ufree.le_rothNumberNat U (fun _ h => bound h) rfl
  change (D.biUnion T).card ≤ _ at out
  rw [card_biUnion disj] at out
  apply le_trans (le_of_eq ?_) out
  apply sum_congr rfl
  intro x _
  rw [← hcard x, show T x = (H x).image (word x) by rfl, card_image_of_injective]
  intro u v eq
  exact Nat.eq_of_mul_eq_mul_left hL (Nat.add_left_cancel eq)

/-- Weighted Roth bound at a partial radix block, averaged over all rotations. -/
theorem averaged {L : ℕ} [NeZero L] (D : Finset (Fin L))
    (free : ThreeAPFree (D : Set (Fin L))) (q d : ℕ) (hd : d ≤ L) :
    D.card * ((L-d)*rothNumberNat q+d*rothNumberNat (q+1)) ≤ L*rothNumberNat (L*q+d) := by
  classical
  let f (x : Fin L) := rothNumberNat (if x.val<d then q+1 else q)
  have sumrot (x : Fin L) : ∑ t : Fin L, f (x+t) =
      (L-d)*rothNumberNat q+d*rothNumberNat (q+1) := by
    have r := Equiv.sum_comp (Equiv.addLeft x) f
    change (∑ t : Fin L, f (x+t)) = ∑ t : Fin L, f t at r
    rw [r]
    unfold f
    rw [Fin.sum_univ_eq_sum_range (fun i => rothNumberNat (if i<d then q+1 else q))]
    conv_lhs => rw [show L = d+(L-d) by omega, Finset.sum_range_add]
    have h₁ : (∑ i ∈ range d, rothNumberNat (if i<d then q+1 else q)) =
        d*rothNumberNat (q+1) := by
      trans ∑ _i ∈ range d, rothNumberNat (q+1)
      · exact sum_congr rfl fun i hi => by rw [if_pos (mem_range.mp hi)]
      · simp
    simp only [h₁, Nat.not_lt.mpr (Nat.le_add_right _ _), if_false,
      sum_const, card_range, smul_eq_mul]
    omega
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun t _ => packed D free q d t)
  change (∑ t : Fin L, ∑ x ∈ D, f (x+t)) ≤ _ at hs
  rw [Finset.sum_comm] at hs
  simpa [sumrot, Fintype.card_fin] using hs

#print axioms averaged
end Erdos142CyclicFiber
