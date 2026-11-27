import Mathlib

/-!
# A024675: Average of two consecutive odd primes

Source: https://oeis.org/A024675
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(k) = (p + q)/2` for consecutive odd primes `p < q`: `4, 6, 9, 12, …` (offset `1`).
A028334 (offset `2`) lists the differences between consecutive odd primes divided by `2`.
Conjecture (Thomas Ordowski, OEIS, 2022): `∏_{k=1}^{n} a(k) / A028334(k+1)` is an integer for
every `n ≥ 1`.

## Encoding

* With `prime i = Nat.nth Nat.Prime i` (`prime 0 = 2`), `a(k) = (prime k + prime (k+1)) / 2` and
  `A028334(k+1) = (prime (k+1) - prime k) / 2` for `k ≥ 1`.
* "The product of the quotients is an integer" is stated as divisibility of the product of the
  numerators by the product of the denominators.
-/

namespace OMA.S_oeis_a024675

/-- `a(k)`: average of the `k`-th and `(k+1)`-th odd primes. -/
noncomputable def a (k : ℕ) : ℕ := (Nat.nth Nat.Prime k + Nat.nth Nat.Prime (k + 1)) / 2

/-- `A028334(k+1)`: half the gap between the `k`-th and `(k+1)`-th odd primes. -/
noncomputable def d (k : ℕ) : ℕ := (Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k) / 2

end OMA.S_oeis_a024675

namespace Deldor14.PrimeGaps
open Finset OMA.S_oeis_a024675
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
private def P := (trialTab 820).toArray
private def lookup (i : ℕ) := P[i]?.getD 0
private theorem table_length : 130≤(trialTab 820).length := by decide +kernel
private theorem lookup_eq {i : ℕ} (bound : i<130) : lookup i=Nat.nth Nat.Prime i := by
  have h := table_length
  rw [trialTab_eq] at h
  simpa only [lookup,P,trialTab_eq,List.getElem?_toArray] using tab_get 820 i (bound.trans_le h)
private def gap (k : ℕ) := (lookup (k+1)-lookup k)/2
private def avg (k : ℕ) := (lookup k+lookup (k+1))/2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem test : ∀ i : Fin 129,
    (∏ k ∈ Icc 1 i.val,gap k) ∣ ∏ k ∈ Icc 1 i.val,avg k := by decide +kernel
theorem initial (n : ℕ) (hn : n≤128) :
    (∏ k ∈ Icc 1 n,d k) ∣ ∏ k ∈ Icc 1 n,a k := by
  have left : (∏ k ∈ Icc 1 n,d k) = ∏ k ∈ Icc 1 n,gap k := by
    apply prod_congr rfl
    intro k hk
    have h := (mem_Icc.mp hk).2
    rw [d,gap,lookup_eq (by omega),lookup_eq (by omega)]
  have right : (∏ k ∈ Icc 1 n,a k) = ∏ k ∈ Icc 1 n,avg k := by
    apply prod_congr rfl
    intro k hk
    have h := (mem_Icc.mp hk).2
    rw [a,avg,lookup_eq (by omega),lookup_eq (by omega)]
  rw [left,right]
  exact test ⟨n,by omega⟩

/-- The half-sum and half-gap are coprime for every adjacent pair of odd primes. -/
theorem coprime_terms (k : ℕ) (hk : 1≤k) : (d k).Coprime (a k) := by
  let p := Nat.nth Nat.Prime k
  let q := Nat.nth Nat.Prime (k+1)
  have hp : p.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k
  have hq : q.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (k+1)
  have lt : p<q := Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self k)
  have p2 := Nat.nth_strictMono Nat.infinite_setOfPred_prime (show 0<k by omega)
  rw [Nat.nth_prime_zero_eq_two] at p2
  change 2<p at p2
  have op := Nat.odd_iff.mp (hp.odd_of_ne_two p2.ne')
  have oq := Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))
  have plus : a k+d k=q := by change (p+q)/2+(q-p)/2=q;omega
  have minus : a k-d k=p := by change (p+q)/2-(q-p)/2=p;omega
  let g := Nat.gcd (d k) (a k)
  have gd : g∣d k := Nat.gcd_dvd_left .. 
  have ga : g∣a k := Nat.gcd_dvd_right ..
  have gp : g∣p := minus ▸ Nat.dvd_sub ga gd
  have gq : g∣q := plus ▸ dvd_add ga gd
  change g=1
  rcases (Nat.dvd_prime hp).mp gp with h | h
  · exact h
  · rw [h] at gq
    exact False.elim (lt.ne ((Nat.prime_dvd_prime_iff_eq hp hq).mp gq))

/-- When the incoming balance is an integer Q, the next half-gap must
already divide Q, since multiplying by the current half-sum cannot supply it. -/
theorem next_balance (k Q : ℕ) (hk : 1≤k) :
    d k ∣ Q*a k ↔ d k ∣ Q := by
  constructor
  · intro h
    exact (coprime_terms k hk).dvd_of_dvd_mul_right h
  · intro h
    exact dvd_mul_of_dvd_left h _
#print axioms initial
#print axioms coprime_terms
#print axioms next_balance
end Deldor14.PrimeGaps
