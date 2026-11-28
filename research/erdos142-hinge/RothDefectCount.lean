import RothExactDefects

open Finset

namespace Erdos142ExactDefects

/-- Disjoint pairs (t,2t) in the first 4^k*w positive integers. -/
theorem dyadic_matching (k w : ℕ) : ∃ T : Finset ℕ,
    (∀ u ∈ T, 0 < u ∧ 2*u ≤ 4^k*w) ∧ (∀ u ∈ T, 2*u ∉ T) ∧
    3*T.card+w=4^k*w := by
  induction k with
  | zero => exact ⟨∅,by simp,by simp,by simp⟩
  | succ k ih =>
    obtain ⟨T,ends,nd,cT⟩ := ih
    let H := 4^k*w
    have he : 4^(k+1)*w=4*H := by dsimp [H]; ring
    rw [he]
    let V := Ioc H (2*H)
    have small {u} (hu : u ∈ T) : 0<u ∧ 2*u ≤ H := ends u hu
    have big {u} (hu : u ∈ V) : H<u ∧ u≤2*H := mem_Ioc.mp hu
    have disj : Disjoint T V := by
      rw [Finset.disjoint_left]
      intro u hu hv
      have := small hu
      have := big hv
      omega
    refine ⟨T ∪ V,?_,?_,?_⟩
    · intro u hu
      rcases mem_union.mp hu with old|new
      · have := small old
        omega
      · have := big new
        omega
    · intro u hu hd
      rcases mem_union.mp hu with old|new <;> rcases mem_union.mp hd with oo|nn
      · exact nd u old oo
      · have := small old
        have := big nn
        omega
      · have := big new
        have := small oo
        omega
      · have := big new
        have := big nn
        omega
    · rw [card_union_of_disjoint disj]
      have cV : V.card=H := by dsimp [V]; rw [Nat.card_Ioc]; omega
      change 3*T.card+w=H at cT
      omega

/-- The finite one-third estimate. The input may have any permitted size
    and C is any family of covers, in particular a family of minimum covers. -/
theorem count_popular (A : Finset ℕ) (C : ℕ → Finset ℕ) (n k w a K : ℕ)
    (fit : A ⊆ range n) (free : ThreeAPFree (↑A : Set ℕ))
    (covers : ∀ d, Covers A (C d) d)
    (gain : K+rothNumberNat (n+4^k*w)+4*a ≤ 2*A.card) :
    K*(4^k*w) ≤ K*w+3*K*((Ioc 0 (4^k*w)).filter (fun d => a < (C d).card)).card +
      18*A.card*rothNumberNat (4^k*w+1) := by
  classical
  let H := 4^k*w
  let G := (Ioc 0 H).filter (fun d => a < (C d).card)
  obtain ⟨T,ends,nd,cT⟩ := dyadic_matching k w
  let bad := T.filter (fun t => (C t).card ≤ a ∧ (C (2*t)).card ≤ a)
  let good := T \ bad
  let pick (t : ℕ) := if (C t).card ≤ a then 2*t else t
  have inG {t} (ht : t ∈ good) : pick t ∈ G := by
    obtain ⟨hT,hb⟩ := mem_sdiff.mp ht
    have e : 0<t ∧ 2*t≤H := ends t hT
    have fail : ¬((C t).card ≤ a ∧ (C (2*t)).card ≤ a) :=
      fun h => hb (mem_filter.mpr ⟨hT,h⟩)
    apply mem_filter.mpr
    dsimp only [pick]
    split <;> constructor <;> first | apply mem_Ioc.mpr <;> omega | omega
  have inj : Set.InjOn pick (↑good : Set ℕ) := by
    intro t ht u hu eq
    have hT := (mem_sdiff.mp ht).1
    have hU := (mem_sdiff.mp hu).1
    dsimp only [pick] at eq
    split_ifs at eq
    · omega
    · exact False.elim (nd t hT (eq.symm ▸ hU))
    · exact False.elim (nd u hU (eq ▸ hT))
    · exact eq
  have gsize : good.card ≤ G.card := by
    rw [← card_image_of_injOn inj]
    exact card_le_card (fun d hd => by
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hd
      exact inG ht)
  have err : bad.card*K ≤ 6*A.card*rothNumberNat (H+1) := calc
    _ = ∑ _t ∈ bad, K := by simp
    _ ≤ ∑ t ∈ bad, 2*(badStarts A t).card := by
      apply sum_le_sum
      intro t ht
      obtain ⟨hT,h1,h2⟩ := mem_filter.mp ht
      obtain ⟨tp,small⟩ := ends t hT
      have E := two_cover_bound A (C t) (C (2*t)) n t tp fit free (covers _) (covers _)
      have mono := rothNumberNat.monotone (show n+t ≤ n+4^k*w by omega)
      omega
    _ ≤ ∑ t ∈ range (H+1), 2*(badStarts A t).card := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro t ht
        have e : 2*t≤H := (ends t (mem_filter.mp ht).1).2
        exact mem_range.mpr (by omega)
      · intros
        omega
    _ ≤ _ := by
      rw [← mul_sum]
      have total := sum_badStarts A free (H+1) 0 1 (by decide)
      simp only [one_mul,zero_add] at total
      nlinarith only [total]
  have sub : bad ⊆ T := filter_subset _ _
  have size : good.card+bad.card=T.card := card_sdiff_add_card_eq_card sub
  have sm := Nat.mul_le_mul_left (3*K) gsize
  have ce := congrArg (fun x => K*x) cT
  have cs := congrArg (fun x => 3*K*x) size
  change K*H ≤ K*w+3*K*G.card+18*A.card*rothNumberNat (H+1)
  change K*(3*T.card+w)=K*H at ce
  nlinarith only [sm,ce,cs,err]

#print axioms dyadic_matching
#print axioms count_popular

end Erdos142ExactDefects
