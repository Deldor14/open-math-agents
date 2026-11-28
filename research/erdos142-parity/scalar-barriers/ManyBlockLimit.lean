import LongGluing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic

/-! A necessary length bound for direct gluing of arbitrary progression-free
subsets of consecutive intervals. Coordinates start at zero. -/

namespace Erdos142ManyBlock
open Finset ProgressionParity

/-- The two intervals are [0,w) and [w+g,w+g+v), with g possibly zero. -/
def SafeJoin (k w g v : ℕ) : Prop :=
  ∀ A B : Finset ℕ, A ⊆ range w → B ⊆ Ico (w+g) (w+g+v) →
    Free (· ∈ A) k → Free (· ∈ B) k → Free (· ∈ A ∪ B) k

private theorem free_of_card_lt {A : Finset ℕ} {k : ℕ} (h : A.card < k) :
    Free (· ∈ A) k := by
  intro a d hd steps
  have incl : (range k).image (fun i => a+i*d) ⊆ A := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact (run_iff_forall _ _ _ _).mp steps i (mem_range.mp hi)
  have c := card_le_card incl
  rw [card_image_of_injective _ (by
    intro i j eq
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel eq)),card_range] at c
  omega

/-- Capacity on the side of a boundary-anchored progression of step s. -/
def capacity (w s : ℕ) := (w-1)/s+1

/-- If the two capacities sum to at least k, exactly k terms straddling the
gap give a counterexample. Both pieces have strictly fewer than k terms. -/
theorem adjacent_capacity {k w g v : ℕ} (hk : 2 ≤ k) (hw : 0 < w)
    (hv : 0 < v) (safe : SafeJoin k w g v) :
    capacity w (g+1) + capacity v (g+1) ≤ k-1 := by
  by_contra! over
  let s := g+1
  let c := min (k-1) (capacity w s)
  change k-1 < capacity w s+capacity v s at over
  have lwpos : 0 < capacity w s := Nat.zero_lt_succ _
  have rwpos : 0 < capacity v s := Nat.zero_lt_succ _
  have cpos : 0 < c := lt_min (by omega) lwpos
  have csmall : c < k := lt_of_le_of_lt (min_le_left _ _) (by omega)
  have ca' : c ≤ capacity w s := min_le_right _ _
  change c ≤ (w-1)/s+1 at ca'
  have ca : c-1 ≤ (w-1)/s := by omega
  have cb' : k-c ≤ capacity v s := by
    by_cases lt : k-1 ≤ capacity w s
    · change k-min (k-1) (capacity w s) ≤ capacity v s
      rw [min_eq_left lt]
      omega
    · change k-min (k-1) (capacity w s) ≤ capacity v s
      rw [min_eq_right (by omega)]
      omega
  change k-c ≤ (v-1)/s+1 at cb'
  have cb : k-c-1 ≤ (v-1)/s := by omega
  have cap₁ : (c-1)*s ≤ w-1 :=
    (Nat.le_div_iff_mul_le (by dsimp [s];omega)).mp ca
  have cap₂ : (k-c-1)*s ≤ v-1 :=
    (Nat.le_div_iff_mul_le (by dsimp [s];omega)).mp cb
  let a := w-1-(c-1)*s
  let f := fun i : ℕ => a+i*s
  have lastL : a+(c-1)*s = w-1 := by dsimp [a];omega
  have firstR : a+c*s = w+g := by
    have e : c*s = (c-1)*s+s := by
      rw [← Nat.succ_mul, show (c-1).succ = c by omega]
    rw [e, ← Nat.add_assoc, lastL]
    change w-1+(g+1)=w+g
    omega
  let A := (range c).image f
  let B := (Ico c k).image f
  have inclA : A ⊆ range w := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    have h := Nat.mul_le_mul_right s (show i ≤ c-1 by
      have := mem_range.mp hi
      omega)
    exact mem_range.mpr (by dsimp [f];omega)
  have inclB : B ⊆ Ico (w+g) (w+g+v) := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    obtain ⟨lo,hi⟩ := mem_Ico.mp hi
    have e : f i = w+g+(i-c)*s := by
      rw [← firstR, Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_of_le lo]
    have bound := Nat.mul_le_mul_right s (show i-c ≤ k-c-1 by omega)
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  have ac : A.card < k := lt_of_le_of_lt card_image_le (by simpa using csmall)
  have bc : B.card < k := lt_of_le_of_lt card_image_le (by
    rw [Nat.card_Ico]; omega)
  have avoid := safe A B inclA inclB (free_of_card_lt ac) (free_of_card_lt bc)
  apply avoid a s (by dsimp [s]; omega)
  apply (run_iff_forall _ _ _ _).mpr
  intro i hi
  by_cases h : i < c
  · exact mem_union_left _ (mem_image_of_mem f (mem_range.mpr h))
  · exact mem_union_right _ (mem_image_of_mem f (mem_Ico.mpr ⟨by omega,hi⟩))

private theorem width_le {w s : ℕ} (hw : 0 < w) (hs : 0 < s) :
    w ≤ capacity w s * s := by
  have h : w-1 < ((w-1)/s+1)*s := (Nat.div_lt_iff_lt_mul hs).mp (by omega)
  dsimp [capacity]
  omega

theorem adjacent_widths {k w g v : ℕ} (hk : 2 ≤ k) (hw : 0 < w)
    (hv : 0 < v) (safe : SafeJoin k w g v) :
    w+v ≤ (k-1)*(g+1) ∧ w ≤ (k-2)*(g+1) ∧ v ≤ (k-2)*(g+1) := by
  have h := adjacent_capacity hk hw hv safe
  have lw := width_le hw (show 0 < g+1 by omega)
  have rw' := width_le hv (show 0 < g+1 by omega)
  have leftpos : 0 < capacity w (g+1) := by simp [capacity]
  have rightpos : 0 < capacity v (g+1) := by simp [capacity]
  refine ⟨?_,lw.trans (Nat.mul_le_mul_right _ (by omega)),
    rw'.trans (Nat.mul_le_mul_right _ (by omega))⟩
  have e := Nat.mul_le_mul_right (g+1) h
  rw [Nat.add_mul] at e
  omega

/-- For n+1 nonempty blocks (n ≥ 2), twice their combined width is at most
(2k−3) times the total gaps, with one lattice correction per gap. -/
theorem many_block_limit {k n : ℕ} (hk : 3 ≤ k) (hn : 2 ≤ n)
    (w g : ℕ → ℕ) (hw : ∀ i ≤ n, 0 < w i)
    (safe : ∀ i < n, SafeJoin k (w i) (g i) (w (i+1))) :
    2 * (∑ i ∈ range (n+1), w i) ≤ (2*k-3)*((∑ i ∈ range n, g i)+n) := by
  have H (i : ℕ) (hi : i < n) :=
    adjacent_widths (by omega : 2 ≤ k) (hw i (by omega)) (hw (i+1) (by omega)) (safe i hi)
  let s := fun i => g i+1
  let gaps := ∑ i ∈ range n, s i
  have gap_eq : gaps = (∑ i ∈ range n, g i)+n := by simp [gaps,s,sum_add_distrib]
  have pairs : (∑ i ∈ range n, (w i+w (i+1))) ≤ (k-1)*gaps := by
    dsimp [gaps]
    rw [mul_sum]
    exact sum_le_sum (fun i hi => (H i (mem_range.mp hi)).1)
  have counts : (∑ i ∈ range n, (w i+w (i+1))) + w 0 + w n =
      2*(∑ i ∈ range (n+1), w i) := by
    rw [sum_add_distrib]
    have L := sum_range_succ w n
    have R := sum_range_succ' w n
    omega
  have end_gaps : s 0 + s (n-1) ≤ gaps := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp only [Nat.succ_sub_one, gaps, sum_range_succ]
    have h := single_le_sum (f := s) (fun i _ => Nat.zero_le (s i)) (mem_range.mpr (by omega : 0<t))
    omega
  have endpoints : w 0 + w n ≤ (k-2)*gaps := by
    have a := (H 0 (by omega)).2.1
    have b := (H (n-1) (by omega)).2.2
    rw [Nat.sub_one_add_one_eq_of_pos (by omega)] at b
    have e := Nat.mul_le_mul_left (k-2) end_gaps
    rw [Nat.mul_add] at e
    dsimp [s] at e
    omega
  rw [← gap_eq, show 2*k-3=(k-1)+(k-2) by omega,Nat.add_mul]
  omega

/-- The many-block limiting dilation exceeds 1+d when h=k−2≥1 and
h*d*(1+d)=1, the fixed point for two asymmetric blocks. -/
theorem strictly_above_two_block {h d : ℝ} (hh : 1 ≤ h) (hd : 0 < d)
    (root : h*d*(1+d)=1) : d < 2/(2*h+1) := by
  have bound : d < 1 := by
    by_contra! bad
    have hd1 := mul_le_mul_of_nonneg_right hh hd.le
    nlinarith [mul_nonneg (sub_nonneg.mpr bad) (show 0 ≤ h*d by positivity)]
  have half : 1/2 < h*d := by
    nlinarith [mul_pos (show 0 < h*d by positivity) (sub_pos.mpr bound)]
  apply (lt_div_iff₀ (by positivity)).mpr
  nlinarith [mul_pos (sub_pos.mpr half) hd]

/-- For a globally safe layout, one point per block yields a progression-free
set of representatives. In an interval of span L its size is at most R_k(L). -/
theorem representatives_bound {k m L : ℕ} (hk : 2 ≤ k)
    (blocks : Fin m → Finset ℕ) (inside : ∀ i, blocks i ⊆ Icc 1 L)
    (safe : ∀ S : Fin m → Finset ℕ, (∀ i, S i ⊆ blocks i) →
      (∀ i, Free (· ∈ S i) k) → Free (· ∈ univ.biUnion S) k)
    (f : Fin m → ℕ) (mem : ∀ i, f i ∈ blocks i) (inj : Function.Injective f) :
    m ≤ Set.IsAPOfLengthFree.maxCard k L := by
  have rep := safe (fun i => {f i})
    (fun i => singleton_subset_iff.mpr (mem i))
    (fun _ => free_of_card_lt (by rw [card_singleton];omega))
  have eq : univ.biUnion (fun i => {f i}) = univ.image f := by ext x; simp [eq_comm]
  rw [eq] at rep
  have incl : univ.image f ⊆ Icc 1 L := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact inside i (mem i)
  have bound := bound_witness (by omega : 1 < k) (univ.image f) incl rep
  simpa [card_image_of_injective _ inj] using bound

#print axioms representatives_bound
#print axioms adjacent_capacity
#print axioms many_block_limit
#print axioms strictly_above_two_block
end Erdos142ManyBlock
