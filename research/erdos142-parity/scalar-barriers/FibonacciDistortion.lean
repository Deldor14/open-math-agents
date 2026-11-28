import PlateauRigidity
import Mathlib.Data.Nat.Fib.Basic

/-! Finite distortion at consecutive Fibonacci endpoints, by iterating
the half-height rigidity of a scalar splitting and gluing profile. -/

namespace Erdos142FibonacciDistortion
open Set

def endpoints : ℕ → ℕ × ℕ
  | 0 => (1,1)
  | s+1 =>
    let p := endpoints s
    (p.1+p.2,p.1+2*p.2)

abbrev u (s : ℕ) := (endpoints s).1
abbrev v (s : ℕ) := (endpoints s).2

theorem fibonacci (s : ℕ) : u s=Nat.fib (2*s+1) ∧ v s=Nat.fib (2*s+2) := by
  induction s with
  | zero => decide
  | succ s ih =>
    change u s+v s = _ ∧ u s+2*v s=_
    rw [ih.1,ih.2]
    have next : Nat.fib (2*(s+1)+1)=Nat.fib (2*s+1)+Nat.fib (2*s+2) := by
      simpa only [show 2*(s+1)+1=(2*s+1)+2 by omega,
        show 2*s+1+1=2*s+2 by omega] using (@Nat.fib_add_two (2*s+1))
    have later : Nat.fib (2*(s+1)+2)=Nat.fib (2*s+2)+Nat.fib (2*(s+1)+1) := by
      simpa only [show 2*(s+1)+2=(2*s+2)+2 by omega,
        show 2*(s+1)+1=(2*s+2)+1 by omega] using (@Nat.fib_add_two (2*s+2))
    omega

variable {F : ℝ → ℝ}
    (mono : MonotoneOn F (Ici 0)) (cont : ContinuousOn F (Ici 0))
    (sub : ∀ x ≥ 0, ∀ y ≥ 0, F (x+y) ≤ F x+F y)
    (glue : ∀ x ≥ 0, ∀ y ≥ 0, F x+F y ≤ F (x+y+max x y))

include mono cont sub glue

theorem forced_height (s : ℕ) (flat : F (u s) = F (v s)) :
    (2:ℝ)^s * F 1 = F (u s) := by
  induction s with
  | zero => simp [u,endpoints]
  | succ s smaller =>
    have left : (u (s+1):ℝ)=(u s:ℝ)+v s := by
      change ((u s+v s:ℕ):ℝ)=_
      push_cast; rfl
    have right : (v (s+1):ℝ)=(u s:ℝ)+2*v s := by
      change ((u s+2*v s:ℕ):ℝ)=_
      push_cast; rfl
    have ordered : (u s:ℝ) ≤ v s := by
      exact_mod_cast (show u s ≤ v s by
        rw [(fibonacci s).1,(fibonacci s).2]
        exact Nat.fib_mono (by omega))
    have lo : 0 ≤ (u s:ℝ) := Nat.cast_nonneg _
    rw [left,right] at flat
    have half := Erdos142Rigidity.plateau_half mono sub glue lo ordered
      (cont.mono (fun _ hx => lo.trans hx.1)) flat
    have low := half _ (left_mem_Icc.mpr ordered)
    have high := half _ (right_mem_Icc.mpr ordered)
    have inner := smaller (low.trans high.symm)
    rw [left,pow_succ]
    linarith only [low,inner]

theorem distortion_bound (s : ℕ) (flat : F (u s)=F (v s)) {K r : ℝ}
    (pos : 0 < F (u s)) (seed : r*F 1 ≤ K*F (u s)) : r ≤ K*(2:ℝ)^s := by
  have height := forced_height mono cont sub glue s flat
  have p : 0 < F 1 := by
    by_contra! neg
    have h := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (2:ℝ)^s by positivity) neg
    linarith only [h,height,pos]
  rw [← height,← mul_assoc] at seed
  exact (mul_le_mul_iff_left₀ p).mp seed

#print axioms fibonacci
#print axioms forced_height
#print axioms distortion_bound
end Erdos142FibonacciDistortion
