import OMAStatements.S_oeis_a127711
import Mathlib

open Matrix OMA.S_oeis_a127711

theorem OMA.solution : type_of% @OMA.S_oeis_a127711.main := by
  intro N i j
  let B : Matrix (Fin (N+1)) (Fin (N+1)) ℤ := fun x y =>
    if y.val≤x.val ∧ x.val≤2*y.val then 1 else 0
  let D : Matrix (Fin (N+1)) (Fin (N+1)) ℚ :=
    diagonal (fun (x : Fin (N+1)) => (Nat.fib (x.val+1):ℚ))
  let F : Matrix (Fin (N+1)) (Fin (N+1)) ℤ →+* Matrix (Fin (N+1)) (Fin (N+1)) ℚ :=
    (Int.castRingHom ℚ).mapMatrix
  have low : B.IsLowerTriangular := by
    intro x y h
    have xy : x.val < y.val := h
    exact if_neg (fun hh => (Nat.not_le_of_gt xy) hh.1)
  have det : B.det=1 := by
    rw [Matrix.det_of_isLowerTriangular B low]
    simp [B,Nat.le_mul_of_pos_left]
  have row : D*triangle N=F B := by
    ext x y
    change (D * triangle N) x y = ((B x y:ℤ):ℚ)
    unfold D
    rw [diagonal_mul]
    have nz : (Nat.fib (x.val+1):ℚ)≠0 := by exact_mod_cast (Nat.fib_pos.mpr (Nat.succ_pos _)).ne'
    by_cases h : y.val≤x.val ∧ x.val≤2*y.val
    · simp only [triangle,B,if_pos h,Int.cast_one,mul_inv_cancel₀ nz]
    · simp only [triangle,B,if_neg h,Int.cast_zero,mul_zero]
  have inv : (triangle N)⁻¹=F B⁻¹*D := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc,row,←map_mul,Matrix.nonsing_inv_mul B (by simp [det]),map_one]
  refine ⟨B⁻¹ i j * Nat.fib (j.val+1),?_⟩
  rw [inv]
  unfold D
  rw [mul_diagonal]
  push_cast
  rfl
