import FastPropagation

/-! The concrete fast-chain certificate for the 51-stage grid. -/
namespace Erdos142ExactGrid
open Erdos142Fast
def a₀ : ℕ := 310770333235196810553983
def b₀ : ℕ := 305914546778396860389078
def A : ℕ := 461814143304116035103818818074847139530008111
def B : ℕ := 747230980351474411985551361801500529348765790
def E : ℕ := 631084599572840308301591625232753170418978652562432302171547124947562274392683852722113703894431253452928422652401678444380668341347
def Q : ℕ := 2251799813685248
def C : ℕ := 2303115151489024
def M : ℕ := 2401732030400183044439
def D : ℕ := 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def seedThreshold : ℕ := 1314292663973053677518173
def counts : List ℕ := [0, 155, 158, 161, 163, 166, 169, 171, 174, 177, 180, 183, 185, 188, 191, 194, 197, 199, 202, 205, 208, 211, 213, 216, 219, 221, 224, 227, 230, 233, 235, 238, 241, 244, 247, 249, 252, 255, 258, 261, 263, 266, 269, 271, 274, 277, 280, 283, 285, 288, 291]
def initial : Row := ⟨a₀,b₀,1,0⟩
def finalRow : Row := ⟨A,B,Q,E⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem checked : accepts initial counts = true := by decide +kernel
set_option maxRecDepth 6000 in
theorem end_row : finish initial counts = finalRow := by decide +kernel

theorem golden : A < B ∧ (B+1)^2 < A*(B+1)+A^2 := by decide +kernel

theorem coefficients : 2*(C*E+Q) ≤ (C-Q)*D ∧ Q < C := by decide +kernel

theorem abstract (F : ℕ → ℤ) (mono : Monotone F)
    (sub : ∀ x y, F (x+y) ≤ F x + F y)
    (glue : ∀ x y, y ≤ x → F x + F y ≤ F (2*x+y))
    (seed : (C:ℤ)*F a₀ ≤ F B) : 2*F A ≤ (D:ℤ)*(F B-F A) := by
  have base : Bound F a₀ initial := by simp [Bound,initial]
  have h := run F mono sub glue a₀ initial counts base checked
  rw [end_row] at h
  change F A ≤ (Q:ℤ)*F a₀+(E:ℤ)*(F B-F A) at h
  have z := mul_le_mul_of_nonneg_left h (Int.natCast_nonneg C)
  have w := mul_le_mul_of_nonneg_left seed (Int.natCast_nonneg Q)
  have dpos : 0 ≤ F B - F A := sub_nonneg.mpr (mono golden.1.le)
  have hq : (Q:ℤ) < C := by exact_mod_cast coefficients.2
  have cn : 2*((C:ℤ)*E+Q) ≤ ((C:ℤ)-Q)*D := by
    decide +kernel
  have z2 : ((C:ℤ)-Q)*F A ≤ ((C:ℤ)*E+Q)*(F B-F A) := by nlinarith only [z,w]
  have enough := mul_le_mul_of_nonneg_right cn dpos
  apply le_of_mul_le_mul_left (a:=((C:ℤ)-Q)) _ (by omega)
  nlinarith only [z2,enough]

#print axioms abstract
end Erdos142ExactGrid
