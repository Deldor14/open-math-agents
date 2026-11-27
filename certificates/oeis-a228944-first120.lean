import Mathlib

/-!
# OEIS A228944: Differences of highly abundant numbers

Source: https://oeis.org/A228944
Credit: @gblacher2

Jaycob Coleman conjectured that every highly composite number `n` is the
difference of two highly abundant numbers, each at most `2 * n`.
-/

namespace OMA.S_oeis_a228944

/-- A positive integer whose divisor count exceeds that of every smaller
positive integer, as in OEIS A002182. -/
def IsHighlyComposite (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → m.divisors.card < n.divisors.card

/-- A positive integer whose divisor sum exceeds that of every smaller
positive integer, as in OEIS A002093. -/
def IsHighlyAbundant (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n →
    ArithmeticFunction.sigma 1 m < ArithmeticFunction.sigma 1 n

end OMA.S_oeis_a228944

namespace Deldor14.RecordDivisors
open OMA.S_oeis_a228944
private def record (f : ℕ → ℕ) (n : ℕ) : Prop :=
  0<n ∧ ∀ j : Fin n, 0<j.val → f j.val < f n
private instance (f : ℕ → ℕ) (n : ℕ) : Decidable (record f n) := by unfold record; infer_instance
private theorem record_iff (f : ℕ → ℕ) (n : ℕ) :
    record f n ↔ 0<n ∧ ∀ j, 0<j → j<n → f j<f n := by
  constructor
  · exact fun h => ⟨h.1, fun j hp hj => h.2 ⟨j,hj⟩ hp⟩
  · exact fun h => ⟨h.1, fun j hp => h.2 _ hp j.isLt⟩
private def tau (n : ℕ) := n.divisors.card
private def sumD (n : ℕ) := ∑ j ∈ n.divisors,j
private theorem abundant (n : ℕ) : record sumD n ↔ IsHighlyAbundant n := by
  simp only [record_iff,IsHighlyAbundant,ArithmeticFunction.sigma_one_apply,sumD]
private theorem composite (n : ℕ) : record tau n ↔ IsHighlyComposite n := record_iff _ _
private def witness : ℕ → ℕ
  | 1 => 1
  | 2 => 1
  | 4 => 2
  | 6 => 2
  | 12 => 4
  | 24 => 6
  | 36 => 6
  | 48 => 12
  | 60 => 12
  | 120 => 24
  | _ => 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checked : ∀ i : Fin 121, record tau i.val →
    record sumD (i.val+witness i.val) ∧ record sumD (witness i.val) ∧ witness i.val ≤ i.val := by
  decide +kernel

/-- Every highly composite number through 120 is a difference of two highly
abundant numbers, both at most twice that highly composite number. -/
theorem initial (n : ℕ) (bound : n≤120) (hn : IsHighlyComposite n) :
    ∃ a b, IsHighlyAbundant a ∧ IsHighlyAbundant b ∧ a≤2*n ∧ b≤2*n ∧ a=b+n := by
  obtain ⟨a,b,le⟩ := checked ⟨n,by omega⟩ ((composite n).mpr hn)
  change witness n ≤ n at le
  exact ⟨n+witness n,witness n,(abundant _).mp a,(abundant _).mp b,by omega,by omega,Nat.add_comm ..⟩
#print axioms initial
end Deldor14.RecordDivisors
