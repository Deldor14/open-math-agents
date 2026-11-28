import Mathlib

/-! Finite counting and deletion for the sampled 3-AP hypergraph.
The code of an increasing progression is its final index and its positive
step. A fibre consisting of consecutive indices has the same code set. -/

namespace Erdos142SparseSampling
open Finset

/-- Codes (last, step) for the nonconstant, increasing 3-APs in [0,s). -/
def codes (s : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (range s).sigma (fun last => Icc 1 (last/2))

theorem encode {s a b c : ℕ} (ab : a < b) (last : c < s) (ap : a+c=b+b) :
    (⟨c,c-b⟩ : Σ _ : ℕ, ℕ) ∈ codes s ∧ c-2*(c-b)=a ∧ c-(c-b)=b := by
  simp only [codes,mem_sigma,mem_range,mem_Icc]
  omega

theorem decode {s : ℕ} {v : Σ _ : ℕ, ℕ} (h : v ∈ codes s) :
    v.1-2*v.2 < v.1-v.2 ∧ v.1-v.2 < v.1 ∧ v.1 < s ∧
      (v.1-2*v.2)+v.1=(v.1-v.2)+(v.1-v.2) ∧ v.1-(v.1-v.2)=v.2 := by
  simp only [codes,mem_sigma,mem_range,mem_Icc] at h
  omega

theorem count (s : ℕ) : (codes s).card = ∑ i ∈ range s, i/2 := by
  simp [codes,card_sigma,Nat.card_Icc]

/-- Four times the number of unoriented edges is at most s(s−1). -/
theorem count_bound (s : ℕ) : 4*(codes s).card+s ≤ s^2 := by
  rw [count]
  induction s with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have even_bound : 4*(n/2) ≤ 2*n := by omega
    nlinarith only [ih,even_bound]

theorem exact_count (n : ℕ) :
    (codes (2*n+1)).card = n^2 ∧ (codes (2*n+2)).card = n*(n+1) := by
  have next (s : ℕ) : (codes (s+1)).card = (codes s).card+s/2 := by
    rw [count,count,sum_range_succ]
  induction n with
  | zero => norm_num [count]
  | succ n ih =>
    have left : (codes (2*(n+1)+1)).card = (n+1)^2 := by
      rw [show 2*(n+1)+1=(2*n+2)+1 by omega,next,ih.2,
        show (2*n+2)/2=n+1 by omega]
      ring
    refine ⟨left,?_⟩
    rw [show 2*(n+1)+2=(2*(n+1)+1)+1 by omega,next,left,
      show (2*(n+1)+1)/2=n+1 by omega]
    ring

/-- Summing the progression bound over all occupied residue classes. -/
theorem fibre_count {ι : Type*} (I : Finset ι) (size : ι → ℕ) (H L : ℕ)
    (span : ∀ i ∈ I, (size i-1)*L ≤ H) :
    (4*L)*(∑ i ∈ I, (codes (size i)).card) ≤ H*(∑ i ∈ I, size i) := by
  rw [mul_sum,mul_sum]
  apply sum_le_sum
  intro i hi
  have bound : 4*(codes (size i)).card ≤ size i*(size i-1) := by
    have h := count_bound (size i)
    cases hS : size i with
    | zero => simp [count]
    | succ n => rw [hS] at h; simp only [Nat.add_sub_cancel]; nlinarith only [h]
  calc (4*L)*(codes (size i)).card = (4*(codes (size i)).card)*L := by ring
       _ ≤ (size i*(size i-1))*L := Nat.mul_le_mul_right L bound
       _ = size i*((size i-1)*L) := Nat.mul_assoc _ _ _
       _ ≤ size i*H := Nat.mul_le_mul_left _ (span i hi)
       _ = H*size i := Nat.mul_comm _ _

/-- Congruence modulo N is ordinary equality in the initial half interval. -/
theorem half_no_wrap {N a b c : ℕ} (ha : 2*a < N) (hb : 2*b < N) (hc : 2*c < N)
    (progression : a+c ≡ b+b [MOD N]) : a+c=b+b := by
  change (a+c)%N=(b+b)%N at progression
  rwa [Nat.mod_eq_of_lt (by omega : a+c<N),Nat.mod_eq_of_lt (by omega : b+b<N)] at progression

/-- Removing one representative of each nonempty forbidden edge leaves an
independent subset with at most one vertex lost per edge. -/
theorem delete_edges {V : Type*} [DecidableEq V] (S : Finset V) (bad : Finset (Finset V))
    (nonempty : ∀ e ∈ bad, e.Nonempty) :
    ∃ T ⊆ S, S.card ≤ T.card+bad.card ∧ ∀ e ∈ bad, ¬e ⊆ T := by
  classical
  let vertex (e : {e // e ∈ bad}) := (nonempty e.val e.property).choose
  let marks := bad.attach.image vertex
  have picked (e : {e // e ∈ bad}) : vertex e ∈ e.val := (nonempty e.val e.property).choose_spec
  have marked (e : {e // e ∈ bad}) : vertex e ∈ marks :=
    mem_image.mpr ⟨e,mem_attach _ _,rfl⟩
  refine ⟨S \ marks,sdiff_subset,?_,?_⟩
  · calc
      S.card ≤ ((S \ marks) ∪ marks).card := card_le_card (by
        intro v hv
        by_cases h : v ∈ marks
        · exact mem_union.mpr (Or.inr h)
        · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨hv,h⟩)))
      _ ≤ (S \ marks).card+marks.card := card_union_le _ _
      _ ≤ _ := Nat.add_le_add_left (by simpa [marks] using card_image_le (s:=bad.attach) (f:=vertex)) _
  · intro e he included
    have present := included (picked ⟨e,he⟩)
    exact (mem_sdiff.mp present).2 (marked ⟨e,he⟩)

#print axioms encode
#print axioms decode
#print axioms count_bound
#print axioms exact_count
#print axioms fibre_count
#print axioms half_no_wrap
#print axioms delete_edges
end Erdos142SparseSampling
