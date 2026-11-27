import OMAStatements.S_mo_452919
import Mathlib

open OMA.S_mo_452919
namespace Deldor14.DeBruijn

private def G : Digraph (Fin 4) where
  Adj u v := (u:ℕ)%2=(v:ℕ)/2
private instance : DecidableRel G.Adj := fun u v =>
  inferInstanceAs (Decidable ((u:ℕ)%2=(v:ℕ)/2))

private theorem cycles (u v : Fin 4) (h : G.Adj u v) : EdgeOnCycle G u v := by
  fin_cases u <;> fin_cases v
  all_goals first
    | exact False.elim ((by decide : ¬_) h)
    | exact ⟨[0],by decide +kernel⟩
    | exact ⟨[3],by decide +kernel⟩
    | exact ⟨[1,2,0],by decide +kernel⟩
    | exact ⟨[2,1],by decide +kernel⟩
    | exact ⟨[3,2,1],by decide +kernel⟩
    | exact ⟨[0,1,2],by decide +kernel⟩
    | exact ⟨[1,2],by decide +kernel⟩
    | exact ⟨[2,1,3],by decide +kernel⟩

private def L : Matrix (Fin 4) (Fin 4) ℂ :=
  fun _ j => if j.val<2 then 1 else -1

theorem result : ¬ (type_of% @OMA.S_mo_452919.main) := by
  intro supp
  obtain ⟨P,d,unit,eq⟩ := supp (Fin 4) G cycles
  have column (j : Fin 4) : P 0 j+P 1 j = P 2 j+P 3 j := by
    have e (i : Fin 4) := congrFun (congrFun eq i) j
    have e0 := e 0
    have e1 := e 1
    have e2 := e 2
    have e3 := e 3
    simp only [Matrix.mul_diagonal] at e0 e1 e2 e3
    norm_num [Matrix.mul_apply,adjMatrix,G,Fin.sum_univ_succ] at e0 e1 e2 e3
    by_cases z : d j=0
    · simp [z] at e0 e1
      linear_combination e0-e1
    · have a : P 0 j=P 2 j := mul_right_cancel₀ z (e0.symm.trans e2)
      have b : P 1 j=P 3 j := mul_right_cancel₀ z (e1.symm.trans e3)
      rw [a,b]
  have kill : L*P=0 := by
    ext i j
    norm_num [Matrix.mul_apply,L,Fin.sum_univ_succ]
    rw [show Fin.succ (2 : Fin 3) = (3 : Fin 4) by decide]
    linear_combination column j
  have nil : L=0 := by
    have h := congrArg (fun B : Matrix (Fin 4) (Fin 4) ℂ => B*P⁻¹) kill
    simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ unit,zero_mul] using h
  have absurd := congrFun (congrFun nil 0) 0
  norm_num [L] at absurd
end Deldor14.DeBruijn

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_452919.main) := Deldor14.DeBruijn.result
