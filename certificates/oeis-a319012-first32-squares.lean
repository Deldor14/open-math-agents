import Mathlib

/-!
# A319012: a(n) = Sum_{i=1..n} prime(n*(i - 1) + i).

Source: https://oeis.org/A319012
Credit: @sntntHb

Conjecture (stated on the OEIS page): `a(2)` and `a(3)` are the only terms that are perfect
squares (`a(2) = 9`, `a(3) = 36`).

Conventions:
- `prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`.
- The offset is 1, so the terms are `a(n)` for `n ≥ 1`.
-/

namespace OMA.S_oeis_a319012

/-- `a(n) = ∑_{i=1}^{n} prime(n*(i-1) + i)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, Nat.nth Nat.Prime (n * (i - 1) + i - 1)

end OMA.S_oeis_a319012

namespace Deldor14.PrimeSquares
open Finset OMA.S_oeis_a319012
private def tab (N : ℕ) := (List.range N).filter (fun k => decide k.Prime)
private theorem tab_len (N : ℕ) : (tab N).length=Nat.count Nat.Prime N := by
  simp only [tab,Nat.count,List.countP_eq_length_filter]
private theorem tab_get (N i : ℕ) (hi : i<(tab N).length) :
    ((tab N)[i]?).getD 0=Nat.nth Nat.Prime i := by
  induction N with
  | zero => simp [tab] at hi
  | succ N ih =>
    have step : tab (N+1) = if N.Prime then tab N ++ [N] else tab N := by
      by_cases h : N.Prime <;> simp [tab,List.range_succ,List.filter_append,h]
    by_cases h : N.Prime
    · rw [step,if_pos h] at hi ⊢
      by_cases old : i<(tab N).length
      · rw [List.getElem?_append_left old]; exact ih old
      · simp only [List.length_append,List.length_cons,List.length_nil] at hi
        have e : i=(tab N).length := by omega
        rw [e,List.getElem?_append_right (by rfl)]
        simp [tab_len,Nat.nth_count h]
    · rw [step,if_neg h] at hi ⊢
      exact ih hi
private def computableSum (T : Array ℕ) (n : ℕ) :=
  ∑ i ∈ Icc 1 n, T[n*(i-1)+i-1]?.getD 0
private theorem equal (N n : ℕ) (hn : n^2 ≤ (tab N).length) :
    a n=computableSum (tab N).toArray n := by
  unfold a computableSum
  apply sum_congr rfl
  intro i hi
  obtain ⟨lo,le⟩ := mem_Icc.mp hi
  have lt : n*(i-1)+i-1 < (tab N).length := by
    have h := Nat.mul_le_mul_left n (show i-1≤n-1 by omega)
    have t : n*(n-1)+n=n^2 := by
      obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
      simp;ring
    omega
  simpa using (tab_get N _ lt).symm
private theorem square_test (a : ℕ) : IsSquare a ↔ a.sqrt^2=a := by
  constructor
  · rintro ⟨b,rfl⟩;simp [pow_two]
  · exact fun h => ⟨_,by rw [← pow_two];exact h.symm⟩
private def trial (n : ℕ) : Bool :=
  decide (2≤n) && (List.range (Nat.sqrt n-1)).all (fun j => n%(j+2) != 0)
private theorem trial_correct (n : ℕ) : trial n=decide n.Prime := by
  apply Bool.eq_iff_iff.mpr
  simp only [trial,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range,
    bne_iff_ne,Nat.prime_def_le_sqrt,Nat.dvd_iff_mod_eq_zero]
  constructor
  · rintro ⟨lo,test⟩
    refine ⟨lo,fun m hm hl => ?_⟩
    obtain ⟨j,rfl⟩ : ∃ j, m=j+2 := ⟨m-2,by omega⟩
    exact test j (by omega)
  · rintro ⟨lo,test⟩
    exact ⟨lo,fun j h => test (j+2) (by omega) (by omega)⟩
private def trialTab (n : ℕ) := (List.range n).filter trial
private theorem trialTab_eq (n : ℕ) : trialTab n=tab n := by
  unfold trialTab tab
  rw [show trial = fun k => decide k.Prime from funext trial_correct]
private def initial := (trialTab 8200).toArray
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem length_initial : 32^2 ≤ (trialTab 8200).length := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem verify_initial : ∀ n : Fin 33, 0<n.val →
   (Nat.sqrt (computableSum initial n.val)^2=computableSum initial n.val ↔ n.val=2 ∨ n.val=3) := by
  decide +kernel
theorem initial_range (n : ℕ) (hn : 1≤n) (bound : n≤32) :
    IsSquare (a n) ↔ n=2 ∨ n=3 := by
  have len : n^2≤(tab 8200).length := (Nat.pow_le_pow_left bound 2).trans (trialTab_eq 8200 ▸ length_initial)
  rw [equal 8200 n len,square_test]
  simpa only [initial,trialTab_eq] using verify_initial ⟨n,by omega⟩ hn
#print axioms initial_range
end Deldor14.PrimeSquares
