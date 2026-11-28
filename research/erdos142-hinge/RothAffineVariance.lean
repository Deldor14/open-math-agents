import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open Finset
namespace Erdos142AffineVariance

private def orderedPair {F : Type*} [Field F] (x y : F) (ne : x≠y) :
    (F × F) ≃ (F × F) where
  toFun ab := (ab.1*x+ab.2,ab.1*y+ab.2)
  invFun uv := ((uv.2-uv.1)/(y-x),uv.1-((uv.2-uv.1)/(y-x))*x)
  left_inv := by
    rintro ⟨a,b⟩
    apply Prod.ext <;> dsimp <;> field_simp [sub_ne_zero.mpr (Ne.symm ne)] <;> ring
  right_inv := by
    rintro ⟨u,v⟩
    apply Prod.ext <;> dsimp <;> field_simp [sub_ne_zero.mpr (Ne.symm ne)] <;> ring

private def onePoint {F : Type*} [Field F] (x : F) : (F × F) ≃ (F × F) where
  toFun ab := (ab.1,ab.1*x+ab.2)
  invFun av := (av.1,av.2-av.1*x)
  left_inv := by rintro ⟨a,b⟩; simp
  right_inv := by rintro ⟨a,v⟩; simp

/-- For all invertible affine maps of a finite field, the second moment of
    any centered real test on the image of a set has the exact finite-
    population correction. The sum on the left is unnormalized. -/
theorem variance {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (A : Finset F) (h : F → ℝ) (zero : ∑ x, h x=0) :
    ∑ a ∈ (univ : Finset F).erase 0, ∑ b : F, (∑ x ∈ A, h (a*x+b))^2 =
      (A.card:ℝ)*(Fintype.card F-A.card)*∑ z : F, (h z)^2 := by
  classical
  have cov (x y : F) :
      ∑ ab : F×F, h (ab.1*x+ab.2)*h (ab.1*y+ab.2) =
        if x=y then (Fintype.card F:ℝ)*∑ z : F, (h z)^2 else 0 := by
    by_cases xy : x=y
    · subst y
      rw [if_pos rfl]
      simp_rw [← sq]
      calc
        _ = ∑ uv : F×F, h uv.2 ^ 2 := (onePoint x).sum_comp (fun uv : F×F => h uv.2 ^ 2)
        _ = _ := by simp [Fintype.sum_prod_type]
    · rw [if_neg xy]
      calc
        _ = ∑ uv : F×F, h uv.1*h uv.2 := (orderedPair x y xy).sum_comp (fun uv : F×F => h uv.1*h uv.2)
        _ = _ := by simp [Fintype.sum_prod_type,← mul_sum,zero]
  have full : ∑ ab : F×F, (∑x ∈ A, h (ab.1*x+ab.2))^2 =
      (A.card:ℝ)*(Fintype.card F)*∑ z : F, (h z)^2 := by
    calc
      _ = ∑ ab : F×F, ∑x ∈ A, ∑y ∈ A, h (ab.1*x+ab.2)*h (ab.1*y+ab.2) := by
        simp only [sq,sum_mul,mul_sum]
        exact sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => mul_comm _ _)))
      _ = ∑x ∈ A, ∑y ∈ A, ∑ ab : F×F, h (ab.1*x+ab.2)*h (ab.1*y+ab.2) := by
        rw [sum_comm]
        exact sum_congr rfl (fun _ _ => sum_comm)
      _ = _ := by simp [cov,mul_assoc]
  rw [Fintype.sum_prod_type] at full
  have split := sum_erase_add (univ : Finset F) (fun a => ∑ b : F, (∑ x ∈ A, h (a*x+b))^2) (mem_univ 0)
  have base : ∑b : F, (∑ x ∈ A, h (0*x+b))^2 = (A.card:ℝ)^2 * ∑ b : F, h b ^ 2 := by
    simp [mul_pow,mul_sum]
  rw [base] at split
  nlinarith only [full,split]

#print axioms variance
end Erdos142AffineVariance
