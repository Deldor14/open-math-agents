import OMAStatements.S_mse_199784
import Mathlib

open OMA.S_mse_199784
namespace Deldor14.AsymmetricGame

private def graph : Matrix (Fin 6) (Fin 6) ℕ := !![0,0,0,1,1,0;
    1,1,1,0,0,0;
    1,1,0,1,0,0;
    0,1,0,0,1,1;
    1,0,1,0,0,1;
    0,1,1,1,0,1]
private def A (i j : Fin 6) : ℝ := 2*(graph i j:ℝ)-1
private noncomputable def mixX (i : Fin 6) : ℝ := ![4,2,1,2,3,1] i/13
private noncomputable def mixY (j : Fin 6) : ℝ := ![3,1,2,2,4,1] j/13
private noncomputable abbrev value : ℝ := -1/13

/-- Count alternating walks starting at each row and each column of the 0-1 matrix. -/
private def walks : ℕ → (Fin 6 → ℕ) × (Fin 6 → ℕ)
  | 0 => (fun _ => 1,fun _ => 1)
  | n+1 => (fun i => ∑ j,graph i j*(walks n).2 j,fun j => ∑ i,graph i j*(walks n).1 i)

private theorem asymmetric : IsTotallyAsymmetric A := by
  intro σ τ preserve
  have edges (i j : Fin 6) : graph (σ i) (τ j)=graph i j := by
    have h := preserve i j
    unfold A at h
    exact_mod_cast (by linarith : (graph (σ i) (τ j):ℝ)=graph i j)
  have invariant (n : ℕ) : (∀ i,(walks n).1 (σ i)=(walks n).1 i) ∧
      (∀ j,(walks n).2 (τ j)=(walks n).2 j) := by
    induction n with
    | zero => exact ⟨fun _ => rfl,fun _ => rfl⟩
    | succ n ih =>
      constructor
      · intro i
        change (∑ j,graph (σ i) j*(walks n).2 j)=_
        rw [← Equiv.sum_comp τ (fun j => graph (σ i) j*(walks n).2 j)]
        simp only [edges,ih.2,walks]
      · intro j
        change (∑ i,graph i (τ j)*(walks n).1 i)=_
        rw [← Equiv.sum_comp σ (fun i => graph i (τ j)*(walks n).1 i)]
        simp only [edges,ih.1,walks]
  have r : ∀ i j,(walks 3).1 i=(walks 3).1 j → i=j := by decide +kernel
  have c : ∀ i j,(walks 3).2 i=(walks 3).2 j → i=j := by decide +kernel
  exact ⟨Equiv.ext (fun i => r _ _ ((invariant 3).1 i)),Equiv.ext (fun j => c _ _ ((invariant 3).2 j))⟩

private theorem px (i : Fin 6) : 0 < mixX i := by fin_cases i <;> norm_num [mixX]
private theorem py (i : Fin 6) : 0 < mixY i := by fin_cases i <;> norm_num [mixY]
private theorem sx : mixX ∈ stdSimplex ℝ (Fin 6) :=
  ⟨fun i => (px i).le,by norm_num [mixX,Fin.sum_univ_succ]⟩
private theorem sy : mixY ∈ stdSimplex ℝ (Fin 6) :=
  ⟨fun j => (py j).le,by norm_num [mixY,Fin.sum_univ_succ]⟩

private theorem col (j : Fin 6) : ∑ i,mixX i*A i j=value := by
  fin_cases j <;> norm_num [Fin.sum_univ_succ,A,graph,mixX,value]
private theorem row (i : Fin 6) : ∑ j,A i j*mixY j=value := by
  fin_cases i <;> norm_num [Fin.sum_univ_succ,A,graph,mixY,value]

private theorem constX {y : Fin 6 → ℝ} (hy : y ∈ stdSimplex ℝ (Fin 6)) : payoff A mixX y=value := by
  unfold payoff
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul,col,← Finset.mul_sum,hy.2,mul_one]
private theorem constY {x : Fin 6 → ℝ} (hx : x ∈ stdSimplex ℝ (Fin 6)) : payoff A x mixY=value := by
  unfold payoff
  simp only [mul_assoc,← Finset.mul_sum,row,← Finset.sum_mul,hx.2,one_mul]

private theorem pureRow (i : Fin 6) (y : Fin 6 → ℝ) :
    payoff A (Pi.single i 1) y=∑ j,A i j*y j := by
  classical
  unfold payoff
  simp only [mul_assoc,← Finset.mul_sum]
  simp [Pi.single_apply,ite_mul]
private theorem pureCol (j : Fin 6) (x : Fin 6 → ℝ) :
    payoff A x (Pi.single j 1)=∑ i,x i*A i j := by
  classical
  unfold payoff
  simp [Pi.single_apply,mul_ite]

theorem result : type_of% @OMA.S_mse_199784.main := by
  refine ⟨6,6,A,by decide,by decide,?_,asymmetric,mixX,mixY,?_,px,py,?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [A,graph]
  · exact ⟨sx,sy,fun x hx => by rw [constY hx,constY sx],fun y hy => by rw [constX sy,constX hy]⟩
  · rintro x y ⟨hx,hy,bestX,bestY⟩
    have v : payoff A x y=value := le_antisymm (by simpa [constY hx] using bestY mixY sy)
      (by simpa [constX hy] using bestX mixX sx)
    have upper (i : Fin 6) : ∑ j,A i j*y j ≤ value := by
      simpa only [pureRow,v] using bestX _ (single_mem_stdSimplex ℝ i)
    have lower (j : Fin 6) : value ≤ ∑ i,x i*A i j := by
      simpa only [pureCol,v] using bestY _ (single_mem_stdSimplex ℝ j)
    have nx := hx.2
    have ny := hy.2
    have lower0 := lower 0
    have lower1 := lower 1
    have lower2 := lower 2
    have lower3 := lower 3
    have lower4 := lower 4
    have lower5 := lower 5
    have upper0 := upper 0
    have upper1 := upper 1
    have upper2 := upper 2
    have upper3 := upper 3
    have upper4 := upper 4
    have upper5 := upper 5
    have six (f : Fin 6 → ℝ) :
        ∑ i,f i=f 0+(f 1+(f 2+(f 3+(f 4+f 5)))) := by
      simp only [Fin.sum_univ_succ,Finset.sum_of_isEmpty,add_zero]
      rfl
    simp only [six] at nx ny lower0 lower1 lower2 lower3 lower4 lower5 upper0 upper1 upper2 upper3 upper4 upper5
    norm_num [A,value,show graph 0 0=0 by decide +kernel,
      show graph 1 0=1 by decide +kernel,
      show graph 2 0=1 by decide +kernel,
      show graph 3 0=0 by decide +kernel,
      show graph 4 0=1 by decide +kernel,
      show graph 5 0=0 by decide +kernel] at lower0
    norm_num [A,value,show graph 0 0=0 by decide +kernel,
      show graph 0 1=0 by decide +kernel,
      show graph 0 2=0 by decide +kernel,
      show graph 0 3=1 by decide +kernel,
      show graph 0 4=1 by decide +kernel,
      show graph 0 5=0 by decide +kernel] at upper0
    norm_num [A,value,show graph 0 1=0 by decide +kernel,
      show graph 1 1=1 by decide +kernel,
      show graph 2 1=1 by decide +kernel,
      show graph 3 1=1 by decide +kernel,
      show graph 4 1=0 by decide +kernel,
      show graph 5 1=1 by decide +kernel] at lower1
    norm_num [A,value,show graph 1 0=1 by decide +kernel,
      show graph 1 1=1 by decide +kernel,
      show graph 1 2=1 by decide +kernel,
      show graph 1 3=0 by decide +kernel,
      show graph 1 4=0 by decide +kernel,
      show graph 1 5=0 by decide +kernel] at upper1
    norm_num [A,value,show graph 0 2=0 by decide +kernel,
      show graph 1 2=1 by decide +kernel,
      show graph 2 2=0 by decide +kernel,
      show graph 3 2=0 by decide +kernel,
      show graph 4 2=1 by decide +kernel,
      show graph 5 2=1 by decide +kernel] at lower2
    norm_num [A,value,show graph 2 0=1 by decide +kernel,
      show graph 2 1=1 by decide +kernel,
      show graph 2 2=0 by decide +kernel,
      show graph 2 3=1 by decide +kernel,
      show graph 2 4=0 by decide +kernel,
      show graph 2 5=0 by decide +kernel] at upper2
    norm_num [A,value,show graph 0 3=1 by decide +kernel,
      show graph 1 3=0 by decide +kernel,
      show graph 2 3=1 by decide +kernel,
      show graph 3 3=0 by decide +kernel,
      show graph 4 3=0 by decide +kernel,
      show graph 5 3=1 by decide +kernel] at lower3
    norm_num [A,value,show graph 3 0=0 by decide +kernel,
      show graph 3 1=1 by decide +kernel,
      show graph 3 2=0 by decide +kernel,
      show graph 3 3=0 by decide +kernel,
      show graph 3 4=1 by decide +kernel,
      show graph 3 5=1 by decide +kernel] at upper3
    norm_num [A,value,show graph 0 4=1 by decide +kernel,
      show graph 1 4=0 by decide +kernel,
      show graph 2 4=0 by decide +kernel,
      show graph 3 4=1 by decide +kernel,
      show graph 4 4=0 by decide +kernel,
      show graph 5 4=0 by decide +kernel] at lower4
    norm_num [A,value,show graph 4 0=1 by decide +kernel,
      show graph 4 1=0 by decide +kernel,
      show graph 4 2=1 by decide +kernel,
      show graph 4 3=0 by decide +kernel,
      show graph 4 4=0 by decide +kernel,
      show graph 4 5=1 by decide +kernel] at upper4
    norm_num [A,value,show graph 0 5=0 by decide +kernel,
      show graph 1 5=0 by decide +kernel,
      show graph 2 5=0 by decide +kernel,
      show graph 3 5=1 by decide +kernel,
      show graph 4 5=1 by decide +kernel,
      show graph 5 5=1 by decide +kernel] at lower5
    norm_num [A,value,show graph 5 0=0 by decide +kernel,
      show graph 5 1=1 by decide +kernel,
      show graph 5 2=1 by decide +kernel,
      show graph 5 3=1 by decide +kernel,
      show graph 5 4=0 by decide +kernel,
      show graph 5 5=1 by decide +kernel] at upper5
    constructor
    · funext i
      fin_cases i
      · change x 0 = 4 / 13
        linarith only [nx,lower0,lower1,lower2,lower3,lower4,lower5]
      · change x 1 = 2 / 13
        linarith only [nx,lower0,lower1,lower2,lower3,lower4,lower5]
      · change x 2 = 1 / 13
        linarith only [nx,lower0,lower1,lower2,lower3,lower4,lower5]
      · change x 3 = 2 / 13
        linarith only [nx,lower0,lower1,lower2,lower3,lower4,lower5]
      · change x 4 = 3 / 13
        linarith only [nx,lower0,lower1,lower2,lower3,lower4,lower5]
      · change x 5 = 1 / 13
        linarith only [nx,lower0,lower1,lower2,lower3,lower4,lower5]
    · funext i
      fin_cases i
      · change y 0 = 3 / 13
        linarith only [ny,upper0,upper1,upper2,upper3,upper4,upper5]
      · change y 1 = 1 / 13
        linarith only [ny,upper0,upper1,upper2,upper3,upper4,upper5]
      · change y 2 = 2 / 13
        linarith only [ny,upper0,upper1,upper2,upper3,upper4,upper5]
      · change y 3 = 2 / 13
        linarith only [ny,upper0,upper1,upper2,upper3,upper4,upper5]
      · change y 4 = 4 / 13
        linarith only [ny,upper0,upper1,upper2,upper3,upper4,upper5]
      · change y 5 = 1 / 13
        linarith only [ny,upper0,upper1,upper2,upper3,upper4,upper5]
end Deldor14.AsymmetricGame

theorem OMA.solution : type_of% @OMA.S_mse_199784.main := Deldor14.AsymmetricGame.result
