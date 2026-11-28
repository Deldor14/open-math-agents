import Mathlib.Tactic

namespace Erdos142Steps

/-- Decoding on the refined cyclic grid. Each label lies in an interval of
half the grid spacing, so the adjacent second difference cannot have a carry. -/
theorem decode (P q z x y w a b c : ℤ) (hP : 0 < P)
    (ha : 0 ≤ a ∧ a < P) (hb : 0 ≤ b ∧ b < P) (hc : 0 ≤ c ∧ c < P)
    (h : 2*P*(x+w-2*y)+(a+c-2*b)=2*P*q*z) :
    x+w-2*y=q*z ∧ a+c=2*b := by
  have id : 2*P*((x+w-2*y)-q*z) = -(a+c-2*b) := by linarith only [h]
  have le : (x+w-2*y)-q*z ≤ 0 := by
    by_contra! ho
    have ho' : 1 ≤ (x+w-2*y)-q*z := ho
    nlinarith [mul_nonneg (show 0 ≤ P by omega)
      (show 0 ≤ ((x+w-2*y)-q*z)-1 by omega)]
  have ge : 0 ≤ (x+w-2*y)-q*z := by
    by_contra! ho
    have ho' : (x+w-2*y)-q*z ≤ -1 := by omega
    nlinarith [mul_nonneg (show 0 ≤ P by omega)
      (show 0 ≤ -1-((x+w-2*y)-q*z) by omega)]
  have hz : (x+w-2*y)-q*z=0 := by omega
  rw [hz, mul_zero] at id
  omega

/-- If the multiples 0,k,...,(k-1)k and every ordinary k-block have a hole,
the long block from 0 to (k-1)k has at least k distinct holes. -/
theorem block_holes (k : ℕ) (hk : 2 ≤ k) (hole : ℕ → Prop) [DecidablePred hole]
    (one : ∀ s : ℕ, ∃ t : ℕ, t < k ∧ hole (s+t))
    (stride : ∃ j : ℕ, j < k ∧ hole (j*k)) :
    k ≤ ((Finset.range ((k-1)*k+1)).filter hole).card := by
  obtain ⟨j,hj,hj0⟩ := stride
  choose t ht hv using one
  let w (i : ℕ) := if i<j then i*k+t (i*k)
    else if i=j then j*k else ((i-1)*k+1)+t ((i-1)*k+1)
  have good (i : ℕ) : hole (w i) := by
    unfold w
    split_ifs <;> first | exact hv _ | exact hj0
  have step (i : ℕ) : w i < w (i+1) := by
    by_cases before : i+1<j
    · have hi : i<j := by omega
      simp only [w,if_pos hi,if_pos before,Nat.add_mul,Nat.one_mul]
      have bound := ht (i*k)
      omega
    · by_cases last : i+1=j
      · subst j
        have hi : i < i+1 := by omega
        simp only [w,if_pos hi,lt_irrefl,if_false,if_true,Nat.add_mul,Nat.one_mul]
        have bound := ht (i*k)
        omega
      · have after : ¬i+1<j := by omega
        by_cases mid : i=j
        · subst j
          simp [w]; omega
        · have hi : ¬i<j := by omega
          have he : (i-1)*k+k=i*k := by
            have hn : i-1+1=i := by omega
            simpa only [Nat.add_mul,Nat.one_mul] using congrArg (fun n => n*k) hn
          simp only [w,if_neg hi,if_neg mid,if_neg after,if_neg last,Nat.add_sub_cancel]
          have bound := ht ((i-1)*k+1)
          omega
  have mono : StrictMono w := strictMono_nat_of_lt_succ step
  have upper (i : ℕ) (hi : i<k) : w i ≤ (k-1)*k := by
    unfold w
    split_ifs with ha hb
    · have hle : i+1 ≤ k-1 := by omega
      have hmid := Nat.mul_le_mul_right k hle
      simp only [Nat.add_mul,Nat.one_mul] at hmid
      have hh := ht (i*k)
      omega
    · exact Nat.mul_le_mul_right k (by omega)
    · have he : (i-1)*k+k=i*k := by
        have hi' : i-1+1=i := by omega
        simpa only [Nat.add_mul,Nat.one_mul] using congrArg (fun n => n*k) hi'
      have hle : i*k ≤ (k-1)*k := Nat.mul_le_mul_right k (by omega)
      have hh := ht ((i-1)*k+1)
      omega
  have emb : Set.InjOn w ↑(Finset.range k) := mono.injective.injOn
  have sub : (Finset.range k).image w ⊆ (Finset.range ((k-1)*k+1)).filter hole := by
    intro n hn
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have h := upper i (Finset.mem_range.mp hi)
      omega),good i⟩
  have hcard := Finset.card_le_card sub
  simpa only [Finset.card_image_of_injOn emb,Finset.card_range] using hcard

#print axioms decode
#print axioms block_holes
end Erdos142Steps
