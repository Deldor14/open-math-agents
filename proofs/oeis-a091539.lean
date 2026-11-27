import OMAStatements.S_oeis_a091539
import Mathlib

open OMA.S_oeis_a091539 Finset

namespace Deldor14.TripleProducts

def u (n : ℕ) : ℤ := 3^n*(n.factorial:ℤ)

theorem u_succ (n : ℕ) : u (n+1)=3*((n:ℤ)+1)*u n := by
  simp only [u,pow_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
  ring

theorem q_succ (n : ℕ) : q (n+1)=q n*(3*(n:ℤ)+1) := by
  simp [q,Finset.prod_range_succ]

theorem b_succ (n : ℕ) : block (n+1)=block n*(3*(n:ℤ)+2) := by
  simp [block,Finset.prod_range_succ]

theorem divisible (k : ℕ) : 6 ∣ u (k+2) ∧ 2 ∣ q (k+2) ∧ 10 ∣ block (k+2) := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    rw [show k+1+2=(k+2)+1 by omega,u_succ,q_succ,b_succ]
    exact ⟨dvd_mul_of_dvd_right ih.1 _,dvd_mul_of_dvd_left ih.2.1 _,
      dvd_mul_of_dvd_left ih.2.2 _⟩

theorem scaled (k : ℕ) : 60*a (k+2) = block (k+2)*(u (k+2)-3*q (k+2)) := by
  obtain ⟨du,dq,db⟩ := divisible k
  obtain ⟨x,hx⟩ := du
  obtain ⟨y,hy⟩ := dq
  have dn : 6 ∣ u (k+2)-3*q (k+2) := ⟨x-y,by rw [hx,hy]; ring⟩
  have first := Int.ediv_mul_cancel db
  have second := Int.ediv_mul_cancel dn
  change 60*(block (k+2)/10*((u (k+2)-3*q (k+2))/6)) = _
  calc
    _ = (block (k+2)/10*10)*((u (k+2)-3*q (k+2))/6*6) := by ring
    _ = _ := by rw [first,second]

end Deldor14.TripleProducts

open Deldor14.TripleProducts

theorem OMA.solution : type_of% @OMA.S_oeis_a091539.main := by
  intro n minimum
  obtain ⟨k,rfl⟩ : ∃ k, n = k+4 := ⟨n-4,by omega⟩
  rw [show k+4-1=k+3 by omega,show k+4-2=k+2 by omega]
  have e0 := scaled k
  have e1 := scaled (k+1)
  have e2 := scaled (k+2)
  change 60*a (k+3) = block ((k+2)+1)*(u ((k+2)+1)-3*q ((k+2)+1)) at e1
  change 60*a (k+4) = block (((k+2)+1)+1)*(u (((k+2)+1)+1)-3*q (((k+2)+1)+1)) at e2
  rw [b_succ,u_succ,q_succ] at e1
  rw [b_succ,u_succ,q_succ,b_succ,u_succ,q_succ] at e2
  push_cast at *
  let A : ℤ := (3*((k:ℤ)+4)-1)*(6*((k:ℤ)+4)-5)
  let B : ℤ := 3*(3*((k:ℤ)+4)-5)*(((k:ℤ)+4)-1)*(3*((k:ℤ)+4)-1)*(3*((k:ℤ)+4)-4)
  change a (k+4)-A*a (k+3)+B*a (k+2)=0
  have zero : 60*(a (k+4)-A*a (k+3)+B*a (k+2))=0 := by
    dsimp [A,B]
    linear_combination e2 - (3*((k:ℤ)+4)-1)*(6*((k:ℤ)+4)-5)*e1 +
      3*(3*((k:ℤ)+4)-5)*(((k:ℤ)+4)-1)*(3*((k:ℤ)+4)-1)*(3*((k:ℤ)+4)-4)*e0
  omega
