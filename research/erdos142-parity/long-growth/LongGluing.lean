import LocalGrowth

/-! Joining a short interval of length at most g to a long one of length at most
(k-2)g, with a gap of g, preserves freedom from nonconstant k-term APs. -/

namespace Erdos142LongGluing
open ProgressionParity Set.IsAPOfLengthFree Finset

theorem glue {k : ℕ} (hk : 3 ≤ k) (a b g : ℕ)
    (ha : a ≤ g) (hb : b ≤ (k-2)*g) :
    maxCard k a + maxCard k b ≤ maxCard k (a+g+b) := by
  obtain ⟨A, Ain, Af, Ac⟩ := attained (by omega : 1 < k) a
  obtain ⟨B, Bin, Bf, Bc⟩ := attained (by omega : 1 < k) b
  let L := a+g
  let T := B.image (fun z => L+z)
  let C := A ∪ T
  have left {z} (h : z ∈ A) : 1 ≤ z ∧ z ≤ a := Finset.mem_Icc.mp (Ain h)
  have right {z} (h : z ∈ T) : L < z ∧ z ≤ L+b ∧ z-L ∈ B := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp h
    have h := Finset.mem_Icc.mp (Bin hv)
    exact ⟨by omega,by omega,by simpa using hv⟩
  have disj : Disjoint A T := by
    apply Finset.disjoint_left.mpr
    intro z h₁ h₂
    have l := left h₁
    have r := right h₂
    dsimp [L] at r
    omega
  have cin : C ⊆ Finset.Icc 1 (a+g+b) := by
    intro z hz
    rcases Finset.mem_union.mp hz with h|h
    · have l := left h
      exact Finset.mem_Icc.mpr ⟨l.1,by omega⟩
    · have r := right h
      dsimp [L] at r
      exact Finset.mem_Icc.mpr ⟨by omega,r.2.1⟩
  have cf : Free (· ∈ C) k := by
    intro u d hd run
    have steps := (run_iff_forall _ _ _ _).mp run
    have start : u ∈ C := by simpa using steps 0 (by omega)
    by_cases first : u ∈ A
    · by_cases small : d ≤ g
      · have allLeft (i : ℕ) (hi : i < k) : u+i*d ∈ A := by
          induction i with
          | zero => simpa using first
          | succ i ih =>
            have prev := left (ih (by omega))
            rcases Finset.mem_union.mp (steps (i+1) hi) with h|h
            · exact h
            · have r := right h
              dsimp [L] at r
              rw [Nat.succ_mul] at r
              omega
        exact Af u d hd ((run_iff_forall _ _ _ _).mpr allLeft)
      · have l := left first
        have s₁ : u+d ∈ C := by simpa using steps 1 (by omega)
        have second : u+d ∈ T := (Finset.mem_union.mp s₁).resolve_left (fun h => by
          have h' := left h
          omega)
        have s := right second
        have last := Finset.mem_Icc.mp (cin (steps (k-1) (by omega)))
        have ident : (k-1)*d = (k-2)*d+d := by
          rw [show k-1=(k-2)+1 by omega, Nat.succ_mul]
        have mult := Nat.mul_le_mul_left (k-2) (show g ≤ d by omega)
        dsimp [L] at s
        omega
    · have r := right ((Finset.mem_union.mp start).resolve_left first)
      apply Bf (u-L) d hd
      apply (run_iff_forall _ _ _ _).mpr
      intro i hi
      have t := (Finset.mem_union.mp (steps i hi)).resolve_left (fun h => by
        have h' := left h
        dsimp [L] at r
        omega)
      have v := (right t).2.2
      rwa [show u+i*d-L = u-L+i*d by omega] at v
  have card : C.card = A.card+B.card := by
    dsimp [C,T] at *
    rw [card_union_of_disjoint disj, card_image_of_injective _ (by intro u v h; dsimp at h;omega)]
  rw [← Ac, ← Bc, ← card]
  exact bound_witness (by omega : 1 < k) C cin cf

#print axioms glue
end Erdos142LongGluing
