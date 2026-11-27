import OMAStatements.S_oeis_a390007
import Mathlib

open OMA.S_oeis_a390007

namespace Deldor14.ThreeRectangles

theorem increase {x l h L H : ℤ} (low : l<L) (high : H<h) :
    spread x L H < spread x l h := by
  unfold spread
  apply max_lt
  · exact lt_of_lt_of_le (by omega : H-L<h-l) (le_max_left _ _)
  · apply max_lt
    · exact lt_of_lt_of_le (by omega : x-L<x-l) ((le_max_left _ _).trans (le_max_right _ _))
    · exact lt_of_lt_of_le (by omega : H-x<h-x) ((le_max_right _ _).trans (le_max_right _ _))

theorem unique_tee (n A B D : ℤ) (size : 3≤n) (a0 : 0<A) (a1 : A<n)
    (b0 : 0<B) (b1 : 2*B<n) (largest : n≤2*B+2)
    (value : defect n (.tee A B) = D) (strip : D<2*n)
    (left : D < (n-B)*(n-(A-1)) - n*(A-1))
    (right : D < n*(A+1) - B*(n-(A+1))) :
    ∃! s, optimal n s := by
  have best : ∀ t, valid n t → t≠.tee A B → D<defect n t := by
    intro t admiss other
    cases t with
    | strips x y z =>
      obtain ⟨_,xy,yz,_⟩ := admiss
      change D<n*(z-x)
      have h := mul_le_mul_of_nonneg_left (by omega : 2≤z-x) (by omega : 0≤n)
      omega
    | tee a b =>
      obtain ⟨apos,asize,bpos,bsize⟩ := admiss
      have limit : b≤B := by omega
      have higher := mul_le_mul_of_nonneg_right (by omega : n-B≤n-b) (by omega : 0≤n-a)
      have lower := mul_le_mul_of_nonneg_right limit (by omega : 0≤n-a)
      change D < spread (n*a) (b*(n-a)) ((n-b)*(n-a))
      rcases lt_trichotomy a A with below | same | above
      · have step := mul_le_mul_of_nonneg_left (by omega : n-(A-1)≤n-a) (by omega : 0≤n-B)
        have x := mul_le_mul_of_nonneg_left (by omega : a≤A-1) (by omega : 0≤n)
        apply lt_of_lt_of_le _ ((le_max_right _ _).trans (le_max_right _ _))
        omega
      · subst a
        have strict : b<B := by
          by_contra! bad
          have eq : b=B := by omega
          exact other (by subst b; rfl)
        have small := mul_lt_mul_of_pos_right strict (by omega : 0<n-A)
        have large := mul_lt_mul_of_pos_right (by omega : n-B<n-b) (by omega : 0<n-A)
        rw [← value]; exact increase small large
      · have step := mul_le_mul_of_nonneg_left (by omega : n-a≤n-(A+1)) (by omega : 0≤B)
        have x := mul_le_mul_of_nonneg_left (by omega : A+1≤a) (by omega : 0≤n)
        apply lt_of_lt_of_le _ ((le_max_left _ _).trans (le_max_right _ _))
        omega
  have ok : valid n (.tee A B) := ⟨a0,a1,b0,b1⟩
  refine ⟨.tee A B,⟨ok,?_⟩,?_⟩
  · intro t vt
    by_cases eq : t=.tee A B
    · rw [eq]
    · rw [value]; exact (best t vt eq).le
  · intro t ht
    by_contra ne
    have no := ht.2 _ ok
    rw [value] at no
    exact (not_lt_of_ge no) (best t ht.1 ne)

theorem four_optimal (a : ℤ) (allowed : a=1 ∨ a=2) : optimal 4 (.tee a 1) := by
  rcases allowed with rfl | rfl <;> constructor
  all_goals try (solve | norm_num [valid])
  all_goals
    intro t ht
    cases t with
    | strips x y z => obtain ⟨hx,hy,hz,tot⟩ := ht; omega
    | tee a b =>
      obtain ⟨ha,ha',hb,hb'⟩ := ht
      have hb1 : b=1 := by omega
      subst b
      interval_cases a <;> norm_num [defect,spread]

end Deldor14.ThreeRectangles
open Deldor14.ThreeRectangles

theorem OMA.solution : type_of% @OMA.S_oeis_a390007.main := by
  intro n bound
  by_cases four : n=4
  · subst n; constructor
    · rintro ⟨s,hs,unique⟩
      have a := unique _ (four_optimal 1 (Or.inl rfl))
      have b := unique _ (four_optimal 2 (Or.inr rfl))
      have eq := a.trans b.symm
      cases eq
    · intro falsehood; exact (falsehood rfl).elim
  · refine ⟨fun _ => four, fun _ => ?_⟩
    let k := n/6
    have rest : n=6*k ∨ n=6*k+1 ∨ n=6*k+2 ∨ n=6*k+3 ∨ n=6*k+4 ∨ n=6*k+5 := by
      dsimp [k]; omega
    rcases rest with h | h | h | h | h | h
    · rw [h]
      apply unique_tee _ (2*k) (3*k-1) (8*k)
      all_goals first | omega | skip
      · simp only [defect,spread,max_def]
        split_ifs <;> ring_nf at * <;> omega
      all_goals ring_nf at * <;> omega
    · rw [h]
      apply unique_tee _ (2*k) (3*k) (5*k+1)
      all_goals first | omega | skip
      · simp only [defect,spread,max_def]
        split_ifs <;> ring_nf at * <;> omega
      all_goals ring_nf at * <;> omega
    · rw [h]
      apply unique_tee _ (2*k+1) (3*k) (8*k+2)
      all_goals first | omega | skip
      · simp only [defect,spread,max_def]
        split_ifs <;> ring_nf at * <;> omega
      all_goals ring_nf at * <;> omega
    · rw [h]
      apply unique_tee _ (2*k+1) (3*k+1) (4*k+2)
      all_goals first | omega | skip
      · simp only [defect,spread,max_def]
        split_ifs <;> ring_nf at * <;> omega
      all_goals ring_nf at * <;> omega
    · rw [h]
      apply unique_tee _ (2*k+1) (3*k+1) (8*k+6)
      all_goals first | omega | skip
      · simp only [defect,spread,max_def]
        split_ifs <;> ring_nf at * <;> omega
      all_goals ring_nf at * <;> omega
    · rw [h]
      apply unique_tee _ (2*k+2) (3*k+2) (5*k+4)
      all_goals first | omega | skip
      · simp only [defect,spread,max_def]
        split_ifs <;> ring_nf at * <;> omega
      all_goals ring_nf at * <;> omega
