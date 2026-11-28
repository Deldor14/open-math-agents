import Mathlib

/-! # Binary weights and the logarithmic separation obstruction

Credit: @Deldor14. Doubling of the digit weights makes carries increase
value, whereas a family of distinct bits adds exactly without any carry.
-/

namespace Erdos142DeficitPower
open Finset

/-- Give an integer the value of the weights of its occupied bits. -/
def value (v : ℕ → ℕ) (n : ℕ) : ℕ := (n.bitIndices.map v).sum

private theorem value_even (v : ℕ → ℕ) (n : ℕ) :
    value v (2*n) = value (fun k => v (k+1)) n := by
  simp [value,List.map_map,Function.comp_def]

private theorem value_odd (v : ℕ → ℕ) (n : ℕ) :
    value v (2*n+1) = v 0 + value (fun k => v (k+1)) n := by
  simp [value,List.map_map,Function.comp_def]

/-- Carrying the lowest bit, including any run of occupied bits above it. -/
theorem add_one (v : ℕ → ℕ) (double : ∀ k, 2*v k ≤ v (k+1)) (n : ℕ) :
    value v n + v 0 ≤ value v (n+1) := by
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    let a:=n/2
    have cases : n=2*a ∨ n=2*a+1 := by dsimp [a];omega
    rcases cases with even|odd
    · rw [even,value_even,value_odd]
      omega
    · have small : a<n := by omega
      have hi:=ih a small (fun k=>v (k+1)) (fun k=>double (k+1))
      have d:=double 0
      rw [odd,value_odd,show 2*a+1+1=2*(a+1) by omega,value_even]
      omega

theorem strict_value (v : ℕ → ℕ) (vpos : 0 < v 0) (double : ∀ k, 2*v k ≤ v (k+1)) :
    StrictMono (value v) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h:=add_one v double n
  omega

/-- Adding the k-th binary place cannot cost less than its assigned weight. -/
theorem add_bit (v : ℕ → ℕ) (double : ∀ k, 2*v k ≤ v (k+1)) (k n : ℕ) :
    value v n + v k ≤ value v (n+2^k) := by
  induction k generalizing v n with
  | zero => simpa using add_one v double n
  | succ k ih =>
    let a:=n/2
    have cases : n=2*a ∨ n=2*a+1 := by dsimp [a];omega
    have h:=ih (fun i=>v (i+1)) (fun i=>double (i+1)) a
    rcases cases with even|odd
    · rw [even,show 2*a+2^(k+1)=2*(a+2^k) by rw [pow_succ]; ring,value_even,value_even]
      exact h
    · rw [odd,show 2*a+1+2^(k+1)=2*(a+2^k)+1 by rw [pow_succ]; ring,value_odd,value_odd]
      omega

private theorem add_list (v : ℕ → ℕ) (double : ∀ k, 2*v k ≤ v (k+1)) (l : List ℕ) (n : ℕ) :
    value v n+(l.map v).sum ≤ value v (n+(l.map (fun k=>2^k)).sum) := by
  induction l generalizing n with
  | nil => simp
  | cons k l ih =>
    have hb:=add_bit v double k n
    have tail:=ih (n+2^k)
    simp only [List.map_cons,List.sum_cons,Nat.add_assoc] at tail ⊢
    omega

theorem value_superadd (v : ℕ → ℕ) (double : ∀ k, 2*v k ≤ v (k+1)) (a b : ℕ) :
    value v a+value v b ≤ value v (a+b) := by
  simpa [value] using add_list v double b.bitIndices a

/-- On sorted distinct indices, there is exact equality for arbitrary weights. -/
theorem without_carries (v : ℕ → ℕ) (bits : List ℕ) (sorted : bits.SortedLT) :
    value v (bits.map (fun k=>2^k)).sum=(bits.map v).sum := by
  rw [value,Nat.bitIndices_sum_map_two_pow sorted]

private theorem iter_separation (u h v : ℕ → ℕ) (l : List ℕ)
    (step : ∀ j k, k ∈ l → 1 ≤ j → u j+v k ≤ u (j+h k)) (j : ℕ) (jp : 1≤j) :
    u j+(l.map v).sum ≤ u (j+(l.map h).sum) := by
  induction l generalizing j with
  | nil => simp
  | cons k l ih =>
    have first:=step j k (by simp) jp
    have rest:=ih (fun n t ht hp=>step n t (by simp [ht]) hp) (j+h k) (by omega)
    simp only [List.map_cons,List.sum_cons,Nat.add_assoc] at rest ⊢
    omega

/-- Each distinct selected bit pays a separate additive surcharge, and the
resulting weights realize a single genuine argument of the inverse clock. -/
theorem separation_excess (v u h e : ℕ → ℕ) (bits : List ℕ) (sorted : bits.SortedLT)
    (inverse : ∀ a t, value v a ≤ t → a ≤ e t)
    (step : ∀ j k, k ∈ bits → 1 ≤ j → u j+v k ≤ u (j+h k))
    (c δ : ℝ) (gap : ∀ k∈bits, c*h k+δ ≤ (2:ℝ)^k) :
    δ*bits.length-c ≤ (e (u (1+(bits.map h).sum)):ℝ)-c*(1+(bits.map h).sum:ℝ) := by
  have hs:=iter_separation u h v bits step 1 (by omega)
  have val:=without_carries v bits sorted
  have count:=inverse (bits.map (fun k=>2^k)).sum (u (1+(bits.map h).sum)) (by omega)
  have sumgap : c*((bits.map h).sum:ℕ)+δ*(bits.length:ℝ) ≤ ((bits.map (fun k=>2^k)).sum:ℕ) := by
    clear hs val count sorted step
    induction bits with
    | nil => simp
    | cons k bits ih =>
      have a:=gap k (by simp)
      have b:=ih (fun t ht=>gap t (by simp [ht]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,Nat.cast_pow,
        Nat.cast_ofNat] at a b ⊢
      linarith
  have cast : (((bits.map (fun k=>2^k)).sum:ℕ):ℝ) ≤ e (u (1+(bits.map h).sum)) := by exact_mod_cast count
  linarith

/-- Floor weights for any fixed geometric ratio a≥2 fit the carry theorem.
For exponent β in (0,1), take a=2^(1/β). -/
noncomputable def geometric (a : ℝ) (k : ℕ) : ℕ := ⌊a^k⌋₊

theorem geometric_double {a : ℝ} (ha : 2 ≤ a) (k : ℕ) :
    2*geometric a k ≤ geometric a (k+1) := by
  apply Nat.le_floor
  push_cast
  have floor_le:=Nat.floor_le (show 0≤a^k by positivity)
  change 2*(⌊a^k⌋₊:ℝ) ≤ a^(k+1)
  calc _ ≤ 2*a^k := by linarith only [floor_le]
       _ ≤ a*a^k := mul_le_mul_of_nonneg_right ha (by positivity)
       _ = _ := by rw [pow_succ,mul_comm]

theorem dyadic_bounds {a : ℝ} (ha : 2 ≤ a) {k n : ℕ}
    (lo : 2^k ≤ n) (hi : n < 2^(k+1)) :
    geometric a k ≤ value (geometric a) n ∧ value (geometric a) n < geometric a (k+1) := by
  have mono:=strict_value (geometric a) (by simp [geometric]) (geometric_double ha)
  constructor
  · simpa [value] using mono.monotone lo
  · simpa [value] using mono hi

end Erdos142DeficitPower
#print axioms Erdos142DeficitPower.strict_value
#print axioms Erdos142DeficitPower.value_superadd
#print axioms Erdos142DeficitPower.without_carries
#print axioms Erdos142DeficitPower.separation_excess
#print axioms Erdos142DeficitPower.geometric_double
#print axioms Erdos142DeficitPower.dyadic_bounds
