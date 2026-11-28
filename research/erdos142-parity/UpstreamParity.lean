import FormalConjecturesForMathlib.Combinatorics.AP.Basic
import ParitySplit

namespace ProgressionParity

theorem run_iff_forall (P : ℕ → Prop) (a d k : ℕ) :
    Run P a d k ↔ ∀ i < k, P (a + i*d) := by
  induction k generalizing a with
  | zero => simp [Run]
  | succ k ih =>
    rw [Run, ih]
    constructor
    · rintro ⟨h₀, hs⟩ i hi
      cases i with
      | zero => simpa using h₀
      | succ j =>
        have hp := hs j (by omega)
        simpa only [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp
    · intro h
      refine ⟨by simpa using h 0 (by omega), ?_⟩
      intro j hj
      have hp := h (j+1) (by omega)
      simpa only [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp

theorem upstream_iff_free (S : Set ℕ) {k : ℕ} (hk : 1 < k) :
    S.IsAPOfLengthFree (k : ℕ∞) ↔ Free (· ∈ S) k := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  constructor
  · intro h a d hd hr
    let f : Fin k → ℕ := fun i => a + (i : ℕ)*d
    have inj : Function.Injective f := by
      intro i j eq
      apply Fin.ext
      have eq' : a+(i : ℕ)*d = a+(j : ℕ)*d := eq
      exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel eq')
    have subset : Set.range f ⊆ S := by
      rintro x ⟨i, rfl⟩
      exact (run_iff_forall (· ∈ S) a d k).mp hr i i.isLt
    apply (not_le_of_gt hk') (h (Set.range f) subset ?_)
    refine ⟨a,d,?_,?_⟩
    · rw [← ENat.card_congr (Equiv.ofInjective f inj)]
      simp [ENat.card_eq_coe_fintype_card]
    · ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨(i : ℕ), by exact_mod_cast i.isLt, by simp [f]⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, by exact_mod_cast hi⟩, by simp [f]⟩
  · intro hf T sub ht
    obtain ⟨a,d,hcard,heq⟩ := ht
    by_cases zero : d=0
    · subst d
      have sing : T = {a} := by
        ext x
        rw [heq]
        constructor
        · rintro ⟨i, hi, rfl⟩
          simp
        · intro hx
          have hx' : x=a := hx
          exact ⟨0, by exact_mod_cast (show 0<k by omega), by simp [hx']⟩
      rw [sing] at hcard
      simpa using hcard.ge
    · exfalso
      apply hf a d (by omega)
      apply (run_iff_forall (· ∈ S) a d k).mpr
      intro i hi
      apply sub
      rw [heq]
      exact ⟨i, by exact_mod_cast hi, by simp⟩

theorem upstream_parity (S : Set ℕ) {m : ℕ} (hm : 0 < m) :
    S.IsAPOfLengthFree ((2*m : ℕ) : ℕ∞) ↔
    Free (Part (· ∈ S) 0) (2*m) ∧ Free (Part (· ∈ S) 1) (2*m) ∧
    (∀ a t, ¬ (Run (Part (· ∈ S) 0) a (2*t+1) m ∧ Run (Part (· ∈ S) 1) (a+t) (2*t+1) m)) ∧
    (∀ a t, ¬ (Run (Part (· ∈ S) 1) a (2*t+1) m ∧ Run (Part (· ∈ S) 0) (a+t+1) (2*t+1) m)) :=
  (upstream_iff_free S (by omega)).trans (free_iff _ m)

#print axioms upstream_parity
end ProgressionParity
