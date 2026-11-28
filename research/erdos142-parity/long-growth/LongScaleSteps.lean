import LongGluing

namespace Erdos142LongGluing
open ProgressionParity Set.IsAPOfLengthFree

theorem one_step {k : ℕ} (hk : 3 ≤ k) (t A B x y g : ℕ) (hx : x ≤ A)
    (hy : y ≤ g) (hz : A-x ≤ (k-2)*g) (hfit : y+g+(A-x) ≤ B) :
    (maxCard k (y*t) : ℤ) - maxCard k (x*t) ≤
      (maxCard k (B*t) : ℤ) - maxCard k (A*t) := by
  have h := glue hk (y*t) ((A-x)*t) (g*t) (Nat.mul_le_mul_right t hy) (by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right t hz)
  have m := interval_mono (by omega : 1<k) (Nat.mul_le_mul_right t hfit)
  simp only [Nat.add_mul] at m
  have s := interval_subadditive (by omega : 1<k) (x*t) ((A-x)*t)
  rw [← Nat.add_mul, Nat.add_sub_of_le hx] at s
  omega

end Erdos142LongGluing
#print axioms Erdos142LongGluing.one_step
