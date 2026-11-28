import PlateauRigidity
import Mathlib.Tactic.Ring

/-! Rigidity at the golden ratio: each normalized plateau forces all
finite binary cylinders. The original golden profile is due to eilamc14.
The arguments here apply to any profile satisfying the scalar inequalities. -/

namespace Erdos142GoldenCylinders
open Set

/-- The displacements (in either the argument or value) selected by the
first n binary digits. The first digit indexes the first positive power. -/
noncomputable def offset (r : ℝ) (bits : ℕ → Bool) : ℕ → ℝ
  | 0 => 0
  | n+1 => offset r bits n + if bits n then r^(n+1) else 0

private theorem offset_nonneg {r : ℝ} (hr : 0 ≤ r) (bits : ℕ → Bool) (n : ℕ) :
    0 ≤ offset r bits n := by
  induction n with
  | zero => simp [offset]
  | succ n ih =>
    rw [offset]
    apply add_nonneg ih
    cases bits n <;> simp [pow_nonneg hr]

private theorem first_sum {z c : ℝ} (left : z*(c+1)=c) (n : ℕ) :
    c*z^(n+1)+z^(n+1)=c*z^n := by
  calc c*z^(n+1)+z^(n+1) = z^n*(z*(c+1)) := by ring
       _ = c*z^n := by rw [left,mul_comm]

private theorem second_sum {z c : ℝ} (right : z*(c+2)=1) (n : ℕ) :
    c*z^(n+1)+2*z^(n+1)=z^n := by
  calc c*z^(n+1)+2*z^(n+1) = z^n*(z*(c+2)) := by ring
       _ = z^n := by rw [right,mul_one]

private theorem twice_half (n : ℕ) : 2*(1/2:ℝ)^(n+1)=(1/2:ℝ)^n := by
  rw [pow_succ]
  ring

variable {F : ℝ → ℝ} {z c : ℝ}

/-- Weak endpoint assumptions 0≤z and 0≤c≤1 suffice. -/
theorem scale_values (mono : MonotoneOn F (Ici 0)) (cont : ContinuousOn F (Ici 0))
    (sub : ∀ x ≥ 0, ∀ y ≥ 0, F (x+y) ≤ F x+F y)
    (glue : ∀ x ≥ 0, ∀ y ≥ 0, F x+F y ≤ F (x+y+max x y))
    (hz : 0 ≤ z) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (left : z*(c+1)=c) (right : z*(c+2)=1) (fc : F c=1) (f1 : F 1=1)
    (n : ℕ) : F (c*z^n)=(1/2:ℝ)^n ∧ F (z^n)=(1/2:ℝ)^n := by
  induction n with
  | zero => simpa using And.intro fc f1
  | succ n ih =>
    have pa : 0 ≤ c*z^(n+1) := mul_nonneg hc (pow_nonneg hz _)
    have ab : c*z^(n+1) ≤ z^(n+1) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (pow_nonneg hz (n+1))
    have h :=
      Erdos142Rigidity.plateau_half mono sub glue pa ab
        (cont.mono (fun _ hx => pa.trans hx.1))
        (by rw [first_sum left,second_sum right,ih.1,ih.2])
    have lo := h _ (left_mem_Icc.mpr ab)
    have hi := h _ (right_mem_Icc.mpr ab)
    rw [first_sum left,ih.1] at lo hi
    constructor <;> linarith only [lo,hi,twice_half n]

/-- Splitting a tight cylinder pins its two inner endpoints. Only
subadditivity and the already-forced elementary heights enter this step. -/
theorem subdivision (sub : ∀ x ≥ 0, ∀ y ≥ 0, F (x+y) ≤ F x+F y)
    (hz : 0 ≤ z) (hc : 0 ≤ c) (left : z*(c+1)=c)
    (scales : ∀ n : ℕ, F (c*z^n)=(1/2:ℝ)^n ∧ F (z^n)=(1/2:ℝ)^n)
    {P v : ℝ} {n : ℕ} (hp : 0 ≤ P) (base : F P=v) (last : F (P+c*z^n)=v+(1/2:ℝ)^n) :
    F (P+z^(n+1))=v+(1/2:ℝ)^(n+1) ∧ F (P+c*z^(n+1))=v+(1/2:ℝ)^(n+1) := by
  have hb := pow_nonneg hz (n+1)
  have ha := mul_nonneg hc hb
  have b := sub P hp _ hb
  have a := sub P hp _ ha
  have lb := sub (P+z^(n+1)) (add_nonneg hp hb) _ ha
  have la := sub (P+c*z^(n+1)) (add_nonneg hp ha) _ hb
  have len := first_sum left n
  rw [show P+z^(n+1)+c*z^(n+1)=P+c*z^n by linarith only [len],last,(scales (n+1)).1] at lb
  rw [show P+c*z^(n+1)+z^(n+1)=P+c*z^n by linarith only [len],last,(scales (n+1)).2] at la
  rw [base,(scales (n+1)).2] at b
  rw [base,(scales (n+1)).1] at a
  constructor <;> linarith only [b,a,lb,la,twice_half n]

/-- Both endpoint values of every binary cylinder. -/
theorem cylinders (sub : ∀ x ≥ 0, ∀ y ≥ 0, F (x+y) ≤ F x+F y)
    (hz : 0 ≤ z) (hc : 0 ≤ c) (left : z*(c+1)=c)
    (scales : ∀ n : ℕ, F (c*z^n)=(1/2:ℝ)^n ∧ F (z^n)=(1/2:ℝ)^n)
    (f0 : F 0=0) (bits : ℕ → Bool) (n : ℕ) :
    F (offset z bits n)=offset (1/2) bits n ∧
    F (offset z bits n+c*z^n)=offset (1/2) bits n+(1/2:ℝ)^n := by
  induction n with
  | zero => simpa [offset] using And.intro f0 (scales 0).1
  | succ n ih =>
    have mid := subdivision sub hz hc left scales (offset_nonneg hz bits n) ih.1 ih.2
    cases flag : bits n with
    | false => simpa [offset,flag] using And.intro ih.1 mid.2
    | true =>
      simp only [offset,flag,ite_true]
      refine ⟨mid.1,?_⟩
      have len := first_sum left n
      rw [show offset z bits n+z^(n+1)+c*z^(n+1)=offset z bits n+c*z^n by linarith only [len],ih.2]
      linarith only [twice_half n]

#print axioms scale_values
#print axioms subdivision
#print axioms cylinders
end Erdos142GoldenCylinders
