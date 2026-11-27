import OMAStatements.S_oeis_a284005
import Mathlib

namespace Deldor14.BinaryBinomial
open OMA.S_oeis_a284005 Finset

private theorem evenW (n : ℕ) : weight (2*n)=weight n := by
  cases n with
  | zero => rfl
  | succ n => simp [weight,Nat.digits_base_mul (by decide : 1<2) (Nat.succ_pos n)]
private theorem oddW (n : ℕ) : weight (2*n+1)=1+weight n := by
  unfold weight
  rw [Nat.add_comm, Nat.digits_add 2 (by decide) 1 n (by decide) (Or.inl one_ne_zero),List.sum_cons]
private theorem twice (n : ℕ) : a (2*n)=(1+weight n)*a n := by
  cases n with
  | zero => simp [weight]
  | succ n =>
    rw [a]
    simp [evenW]
private theorem next (n : ℕ) : a (2*n+1)=(2+weight n)*a n := by
  rw [a,if_neg (by omega),oddW,show (2*n+1)/2=n by omega]
  ring
private theorem shiftW (k n : ℕ) : weight (2^k*n)=weight n := by
  induction k with
  | zero => simp
  | succ k h => simpa [pow_succ',Nat.mul_assoc,evenW] using h
private theorem shift (k n : ℕ) : a (2^k*n)=(1+weight n)^k*a n := by
  induction k with
  | zero => simp
  | succ k h => rw [pow_succ' 2, Nat.mul_assoc,twice,shiftW,h,pow_succ'];ring

theorem result : type_of% @OMA.S_oeis_a284005.main := by
  intro m n
  simp only [shift,oddW,next]
  have h := add_pow (1+weight n) 1 (m+1)
  simp only [one_pow,mul_one,Nat.cast_id] at h
  rw [show 1+(1+weight n)=2+weight n by omega]
  calc
    _ = ((1+weight n)+1)^(m+1)*a n := by rw [pow_succ];ring
    _ = _ := by rw [h,Finset.sum_mul];apply sum_congr rfl;intro i _;ring
end Deldor14.BinaryBinomial
theorem OMA.solution : type_of% @OMA.S_oeis_a284005.main := Deldor14.BinaryBinomial.result
