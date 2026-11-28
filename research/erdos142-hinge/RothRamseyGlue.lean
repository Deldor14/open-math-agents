import RothLongDigitInformation

open Finset
open Erdos142LongDigits
namespace Erdos142RamseyGlue

/-- Every positive-step progression of the given length in [0,n) is met. -/
def Hits (n len : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a q, 0 < q → (∀ j < len, a + j*q < n) → ∃ j < len, a + j*q ∈ A

/-- Consecutive triples propagate the same label along every progression of length ≥ 3. -/
theorem free_glue {ι : Type*} {k : ℕ} (hk : 3 ≤ k) (A : Finset ℕ)
    (tag : ℕ → ι) (seed : ι → Finset ℕ)
    (allowed : ∀ x ∈ A, x ∈ seed (tag x)) (free : ∀ i, Free k (seed i))
    (separate : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x+z=y+y →
      tag x=tag y ∧ tag y=tag z) : Free k A := by
  intro a q hq terms
  let v (i : ℕ) := a+i*q
  have triple (i : ℕ) (hi : i+2<k) :
      tag (v i)=tag (v (i+1)) ∧ tag (v (i+1))=tag (v (i+2)) := by
    apply separate _ (terms _ (by omega)) _ (terms _ (by omega)) _ (terms _ hi)
    ring
  have same (i : ℕ) (hi : i<k) : tag (v i)=tag (v 0) := by
    induction i with
    | zero => rfl
    | succ j ih =>
      have prev := ih (by omega)
      cases j with
      | zero => exact (triple 0 (by omega)).1.symm
      | succ j => exact (triple j (by omega)).2.symm.trans prev
  apply free (tag (v 0)) a q hq
  intro i hi
  rw [← same i hi]
  exact allowed _ (terms i hi)

/-- If every long progression contains a short one in an auxiliary region,
    every blocker for the short length is still a blocker there after gluing. -/
theorem hits_glue {n L ell : ℕ} {H A : Finset ℕ} (aux : ℕ → Prop)
    (subprogression : ∀ a q, 0<q → (∀ j<L, a+j*q<n) →
      ∃ b h, 0<h ∧ ∀ i<ell, b+i*h<L ∧ aux (a+(b+i*h)*q))
    (hit : Hits n ell H) (includeAux : ∀ x ∈ H, aux x → x ∈ A) : Hits n L A := by
  intro a q pos fits
  obtain ⟨b,h,hpos,inside⟩ := subprogression a q pos fits
  have ident (i : ℕ) : (a+b*q)+i*(h*q)=a+(b+i*h)*q := by ring
  obtain ⟨i,ile,mem⟩ := hit (a+b*q) (h*q) (Nat.mul_pos hpos pos) (by
    intro i hi
    rw [ident]
    exact fits _ (inside i hi).1)
  exact ⟨_,(inside i ile).1,includeAux _ (ident i ▸ mem) (inside i ile).2⟩

/-- Translation averaging in finite phase spaces, with arbitrary natural site weights. -/
theorem weighted_retention {Ω : Type*} [Fintype Ω] [Nonempty Ω] (S : Finset ℕ)
    (keep : Ω → ℕ → Bool) (w : ℕ → ℕ) (m : ℕ)
    (marginal : ∀ x ∈ S, (univ.filter (fun b => keep b x = true)).card ≥ m) :
    ∃ b : Ω, m*(∑ x ∈ S, w x) ≤ Fintype.card Ω *
      ∑ x ∈ S, (if keep b x then w x else 0) := by
  classical
  let mass (b : Ω) := ∑ x ∈ S, (if keep b x then w x else 0)
  have avg : m*(∑ x ∈ S, w x) ≤ ∑ b : Ω, mass b := by
    simp only [mass]
    rw [sum_comm, mul_sum]
    apply sum_le_sum
    intro x hx
    rw [← sum_filter]
    simpa using Nat.mul_le_mul_right (w x) (marginal x hx)
  obtain ⟨best,_,top⟩ := Finset.exists_max_image (univ : Finset Ω) mass univ_nonempty
  refine ⟨best, avg.trans ?_⟩
  calc
    ∑ b : Ω, mass b ≤ ∑ _b : Ω, mass best := sum_le_sum (fun b hb => top b hb)
    _ = Fintype.card Ω * mass best := by simp

/-- All labelled extensions together determine the supplied set exactly. -/
theorem patches_injective {ι : Type*} (ambient : Finset ℕ)
    (patch blocker : ι → Finset ℕ)
    (cover : ∀ x ∈ ambient, ∃ i, x ∈ patch i)
    (disjoint : ∀ i, Disjoint (patch i) (blocker i)) :
    Set.InjOn (fun S : Finset ℕ => fun i => (S ∩ patch i) ∪ blocker i)
      {S | S ⊆ ambient} := by
  intro S hS T hT eq
  have extract (X : Finset ℕ) (i : ι) (x : ℕ) (hx : x ∈ patch i) :
      x ∈ (X ∩ patch i) ∪ blocker i ↔ x ∈ X := by
    have out : x ∉ blocker i := fun hb => (Finset.disjoint_left.mp (disjoint i)) hx hb
    simp [hx,out]
  ext x
  by_cases hu : x ∈ ambient
  · obtain ⟨i,hi⟩ := cover x hu
    have e := congrFun eq i
    change (S ∩ patch i) ∪ blocker i = (T ∩ patch i) ∪ blocker i at e
    rw [← extract S i x hi, ← extract T i x hi, e]
  · exact iff_of_false (fun hx => hu (hS hx)) (fun hx => hu (hT hx))

#print axioms patches_injective
#print axioms free_glue
#print axioms hits_glue
#print axioms weighted_retention
end Erdos142RamseyGlue
