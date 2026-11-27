import OMAStatements.S_oeis_a306948
import Mathlib

open OMA.S_oeis_a306948 PowerSeries
namespace Deldor14.LogarithmicEGF

private noncomputable abbrev D := derivative ℚ
private noncomputable def diff (f : PowerSeries ℚ) := D f-f
private noncomputable def term (f : PowerSeries ℚ) (n : ℕ) := (n.factorial:ℚ)*coeff n f

private theorem shiftX (f : PowerSeries ℚ) (n : ℕ) : coeff (n+1) (X*f)=coeff n f := by
  simpa only [pow_one] using coeff_X_pow_mul f 1 n

private theorem geom : (1+X)*D (log ℚ)=1 := by
  rw [deriv_log,add_mul,one_mul]
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [map_add,shiftX,coeff_mk,coeff_one,show n+1≠0 by omega,if_false,pow_succ]
    simp

private theorem deltaExp (f : PowerSeries ℚ) : diff (f*exp ℚ)=D f*exp ℚ := by
  simp [diff,Derivation.leibniz,derivative_exp,smul_eq_mul]; ring

private theorem identity : D (diff (diff egf))+X*D (diff (diff egf))=X*diff (diff egf) := by
  have first : D ((1+X)*log ℚ)=log ℚ+1 := by
    simp only [Derivation.leibniz,smul_eq_mul,geom,map_add,derivative_one,derivative_X,zero_add,mul_one]
    ring
  have h : (1+X)*diff (diff egf)=exp ℚ := by
    rw [egf,deltaExp,first,deltaExp,map_add,derivative_one,add_zero,← mul_assoc,geom,one_mul]
  have der := congrArg (fun f : PowerSeries ℚ => D f) h
  simp only [Derivation.leibniz,smul_eq_mul,map_add,derivative_one,derivative_X,zero_add,mul_one,
    derivative_exp] at der
  rw [← h] at der
  linear_combination der

private theorem nextTerm (f : PowerSeries ℚ) (n : ℕ) : term (D f) n=term f (n+1) := by
  simp only [term,coeff_derivative,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add_one]
  ring

private theorem diffTerm (f : PowerSeries ℚ) (n : ℕ) :
    term (diff f) n=term f (n+1)-term f n := by
  rw [← nextTerm]; simp [term,diff,mul_sub]
private theorem xTerm (f : PowerSeries ℚ) (n : ℕ) : term (X*f) (n+1)=((n:ℚ)+1)*term f n := by
  simp [term,shiftX,Nat.factorial_succ,mul_assoc]

theorem result : type_of% @OMA.S_oeis_a306948.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+4 := ⟨n-4,by omega⟩
  have sumTerm (f g : PowerSeries ℚ) (r : ℕ) : term (f+g) r=term f r+term g r := by
    simp [term,mul_add]
  have eq := congrArg (fun f => term f (k+1)) identity
  simp only [sumTerm,xTerm,nextTerm,diffTerm] at eq
  have ident (n : ℕ) : a n=term egf n := rfl
  simp only [ident,show k+4-1=k+3 by omega,show k+4-2=k+2 by omega,
    show k+4-3=k+1 by omega,show k+4-4=k by omega,Nat.cast_add,Nat.cast_ofNat]
  linear_combination eq

end Deldor14.LogarithmicEGF
theorem OMA.solution : type_of% @OMA.S_oeis_a306948.main := Deldor14.LogarithmicEGF.result
