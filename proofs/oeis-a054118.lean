import OMAStatements.S_oeis_a054118
import Mathlib

/-! The sum of row n is (n+1)!. Adjacent diagonal entries differ by a row sum. -/
namespace Deldor14.TriangleRecurrence
open Finset OMA.S_oeis_a054118
private def row (n : ℕ) := ∑ j ∈ range (n+1),T n j
private lemma tzero (n : ℕ) : T n 0=1 := by cases n <;> rw [T]
private lemma tone (n : ℕ) : T (n+1) 1=row n := by rw [T,row]
private lemma step (n k : ℕ) : T (n+1) (k+2)=T (n+1) (k+1)+row (n+1-(k+2)) := by
  conv_lhs => rw [T]
  rfl
private lemma shift (n k : ℕ) (hk : k+1 ≤ n) :
    T (n+1) (k+2) = row n + T n (k+1) := by
  induction k with
  | zero =>
    obtain ⟨m,rfl⟩ : ∃ m,n=m+1 := ⟨n-1,by omega⟩
    rw [step (m+1) 0,tone,tone]
    simp
  | succ k ih =>
    obtain ⟨m,rfl⟩ : ∃ m,n=m+1 := ⟨n-1,by omega⟩
    rw [step (m+1) (k+1),ih (by omega),step m k]
    have eq : m+1+1-(k+1+2)=m+1-(k+2) := by omega
    rw [eq,add_assoc]
private lemma nextrow (n : ℕ) : row (n+1)=(n+2)*row n := by
  have tail : ∑ k ∈ range n,T (n+1) (k+1+1) = ∑ k ∈ range n,(row n + T n (k+1)) := by
    apply sum_congr rfl
    intro k hk
    exact shift n k (mem_range.mp hk)
  have old : row n=(∑ k ∈ range n,T n (k+1))+1 := by
    rw [row,sum_range_succ',tzero]
  calc row (n+1) = (∑ k ∈ range n,T (n+1) (k+1+1)) + row n + 1 := by
         unfold row
         rw [sum_range_succ',sum_range_succ',tzero,tone]
         rfl
       _ = _ := by
         rw [tail,sum_add_distrib,sum_const,card_range,nsmul_eq_mul]
         nlinarith [old]
private lemma nexta (n : ℕ) (hn : 4 ≤ n) : a (n+1)=row n + a n := by
  unfold a
  obtain ⟨k,hk⟩ : ∃ k,n=k+4 := ⟨n-4,by omega⟩
  subst n
  exact shift (k+4) k (by omega)

theorem result : type_of% @OMA.S_oeis_a054118.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=(k+4)+2 := ⟨n-6,by omega⟩
  have u:=nexta (k+4) (by omega)
  have v:=nexta (k+4+1) (by omega)
  have w:=nextrow (k+4)
  have e : a (k+4+2)+(k+4+2)*a (k+4)=(k+4+2+1)*a (k+4+1) := by rw [v,u,w];ring
  have ei := congrArg (fun t : ℕ => (t:ℤ)) e
  push_cast at ei ⊢
  exact (eq_sub_iff_add_eq).mpr ei
end Deldor14.TriangleRecurrence
theorem OMA.solution : type_of% @OMA.S_oeis_a054118.main := Deldor14.TriangleRecurrence.result
