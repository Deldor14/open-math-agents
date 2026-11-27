import OMAStatements.S_oeis_a303120
import Mathlib

open OMA.S_oeis_a303120
namespace Deldor14.Barker303120

private theorem partialSum (N j : ℕ) (hj : j ≤ N) :
    6*((∑ i ∈ Finset.Icc 1 j,i*(N-i):ℕ):ℚ)=
    3*(N:ℚ)*j*(j+1)-j*(j+1)*(2*j+1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j+1),Nat.cast_add,Nat.cast_mul,
      Nat.cast_sub (by omega : j+1 ≤ N)]
    simp only [Nat.cast_succ]
    linear_combination ih (by omega)

private theorem formula (n : ℕ) :
    (a n:ℚ)=(n:ℚ)^2*(-4+3*(1+(-1)^n)*(n:ℚ)^2+4*(n:ℚ)^4)/48 := by
  have h := partialSum (n^2) (n^2/2) (by omega)
  change 6*(a n:ℚ)=_ at h
  rcases Nat.even_or_odd n with ⟨k,hk⟩ | ⟨k,hk⟩
  · have nk : n=2*k := by omega
    clear hk
    subst n
    have half : (2*k)^2/2=2*k^2 := by rw [show (2*k)^2=2*(2*k^2) by ring];omega
    rw [half] at h
    rw [pow_mul (-1 : ℚ) 2 k]
    norm_num at h ⊢
    linarith
  · have nk : n=2*k+1 := by omega
    clear hk
    subst n
    have half : (2*k+1)^2/2=2*k^2+2*k := by
      rw [show (2*k+1)^2=2*(2*k^2+2*k)+1 by ring];omega
    rw [half] at h
    rw [pow_succ (-1:ℚ) (2*k),pow_mul (-1:ℚ) 2 k]
    norm_num at h ⊢
    linarith

theorem result : type_of% @OMA.S_oeis_a303120.main := by
  refine ⟨fun n _ => formula n,?_⟩
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+13 := ⟨n-13,by omega⟩
  apply (Int.cast_inj (α := ℚ)).mp
  simp only [show k+13-1=k+12 by omega,
    show k+13-2=k+11 by omega,
    show k+13-3=k+10 by omega,
    show k+13-4=k+9 by omega,
    show k+13-5=k+8 by omega,
    show k+13-7=k+6 by omega,
    show k+13-8=k+5 by omega,
    show k+13-9=k+4 by omega,
    show k+13-10=k+3 by omega,
    show k+13-11=k+2 by omega,
    show k+13-12=k+1 by omega]
  push_cast
  simp only [formula,Nat.cast_add,Nat.cast_ofNat,pow_add]
  norm_num
  ring

end Deldor14.Barker303120

theorem OMA.solution : type_of% @OMA.S_oeis_a303120.main := Deldor14.Barker303120.result
