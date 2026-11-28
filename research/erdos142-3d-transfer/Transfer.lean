import Mathlib.Tactic

namespace Erdos142ThreeDTransfer

/-- The translation score is determined by three moments per phase bucket. -/
theorem bucket_score {ι : Type*} (I : Finset ι) (f : ι → ℝ) (K e : ℝ) :
    ∑ i ∈ I, (K-(f i+e)^2) =
    (K-e^2)*I.card-2*e*(∑ i ∈ I, f i)-(∑ i ∈ I, (f i)^2) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one, ih]
    ring

/-- Centering the unused coordinate consumes exactly its variance. -/
theorem centered_step {ι : Type*} (I : Finset ι) (e : ι → ℝ) (K c : ℝ)
    (he : ∑ i ∈ I, e i = 0) :
    ∑ i ∈ I, (K-(c+e i)^2) = (K-c^2)*I.card-∑ i ∈ I, (e i)^2 := by
  simpa [add_comm c, he] using bucket_score I e K c

/-- The computed separation certificate and strict window exclude an AP. -/
theorem strict_window (x y z start width metric : ℝ)
    (hx : x < start+width) (hz : z < start+width) (hy : start ≤ y)
    (hw : 16*width ≤ metric) (hcost : metric ≤ 8*(x+z-2*y)) : False := by linarith

/-- Dyadic kernel preweights need only an upper one-step average, including bad primes. -/
theorem weight_step (a b x y : ℝ) (h : x ≤ a*y) (hb : 0 ≤ b) :
    b*x ≤ (a*b)*y := by nlinarith [mul_le_mul_of_nonneg_left h hb]

end Erdos142ThreeDTransfer
#print axioms Erdos142ThreeDTransfer.bucket_score
#print axioms Erdos142ThreeDTransfer.centered_step
#print axioms Erdos142ThreeDTransfer.strict_window
#print axioms Erdos142ThreeDTransfer.weight_step
