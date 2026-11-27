import OMAStatements.S_oeis_a213243
import Mathlib

namespace Deldor14.FiniteCubes
open OMA.S_oeis_a213243 PowerSeries

private noncomputable def cubeEquiv (K : Type*) [Field K] :
    (powMonoidHom 3 : Kˣ →* Kˣ).range ≃ {x : K // x≠0 ∧ ∃ y : K,y^3=x} where
  toFun x := ⟨x.val.val,Units.ne_zero _,by
    obtain ⟨y,hy⟩ := x.property
    exact ⟨y,congrArg Units.val hy⟩⟩
  invFun x := ⟨Units.mk0 x.val x.property.1,by
    obtain ⟨y,hy⟩ := x.property.2
    have yn : y≠0 := by intro h;rw [h] at hy; exact x.property.1 (by simpa using hy.symm)
    exact ⟨Units.mk0 y yn,Units.ext hy⟩⟩
  left_inv _ := by apply Subtype.ext;apply Units.ext;rfl
  right_inv _ := rfl
private theorem order (n : ℕ) (hn : n≠0) : a n=(2^n-1)/Nat.gcd (2^n-1) 3 := by
  let K := GaloisField 2 n
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [GaloisField.card 2 n hn];positivity)
  unfold a
  rw [← Nat.card_congr (cubeEquiv K), IsCyclic.card_powMonoidHom_range,Nat.card_units,GaloisField.card 2 n hn]
private theorem modThree (k : ℕ) : 2^(2*k)%3=1 := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.mul_succ,pow_add,Nat.mul_mod,ih];decide
private theorem formula (n : ℕ) (hn : 0<n) :
    3*(a n:ℤ)=(2-(-1:ℤ)^n)*((2:ℤ)^n-1) := by
  have g := Nat.div_mul_cancel (Nat.gcd_dvd_left (2^n-1) 3)
  change ((2^n-1)/(2^n-1).gcd 3)*_=2^n-1 at g
  rw [← order n hn.ne'] at g
  have positive : 0<2^n := by positivity
  have hg : (2^n-1).gcd 3=Nat.gcd ((2^n-1)%3) 3 := by rw [Nat.gcd_comm];exact Nat.gcd_rec 3 _
  rcases Nat.even_or_odd n with ⟨k,h⟩|⟨k,h⟩
  · have e : n=2*k := by omega
    have r := modThree k
    rw [← e] at r
    rw [hg,show (2^n-1)%3=0 by omega] at g
    simp only [Nat.gcd_zero_left] at g
    have v := congrArg (fun z : ℕ => (z:ℤ)) g
    push_cast [Nat.cast_sub (by omega : 1≤2^n)] at v
    rw [e,show (-1:ℤ)^(2*k)=1 by rw [pow_mul];norm_num]
    rw [← e]
    linarith
  · have e : n=2*k+1 := by omega
    have r : 2^n%3=2 := by rw [e,pow_succ,Nat.mul_mod,modThree] <;> decide
    rw [hg,show (2^n-1)%3=1 by omega] at g
    simp only [Nat.gcd_one_left,mul_one] at g
    have v := congrArg (fun z : ℕ => (z:ℤ)) g
    push_cast [Nat.cast_sub (by omega : 1≤2^n)] at v
    rw [e,show (-1:ℤ)^(2*k+1)= -1 by rw [pow_succ,pow_mul];norm_num]
    rw [← e]
    linarith
private theorem recurrence (n : ℕ) (hn : 5≤n) :
    (a n:ℤ)=5*a (n-2)-4*a (n-4) := by
  obtain ⟨k,rfl⟩ : ∃ k,n=k+5 := ⟨n-5,by omega⟩
  have q := formula (k+5) (by omega)
  have r := formula (k+3) (by omega)
  have s := formula (k+1) (by omega)
  rw [show k+5-2=k+3 by omega,show k+5-4=k+1 by omega]
  simp only [pow_add] at q r s
  norm_num at q r s
  linarith
private theorem init (n : ℕ) (hn : 0<n) (hs : n≤4) :
    (a n:ℤ)=if n=3 then 7 else if n=4 then 5 else 1 := by
  have h := formula n hn
  interval_cases n <;> norm_num at * <;> omega
private theorem series : mk (fun n => if n=0 then (0:ℤ) else a n) *
        ((X-1)*(X+1)*(2*X-1)*(2*X+1) : PowerSeries ℤ)=X*(2*X^2+X+1) := by
  let b (n : ℕ) : ℤ := if n=0 then 0 else a n
  have h : mk b*((X-1)*(X+1)*(2*X-1)*(2*X+1):PowerSeries ℤ) =
      mk b-(C 5*mk b)*X^2+(C 4*mk b)*X^4 := by simp only [map_ofNat];ring
  have rhs : (X*(2*X^2+X+1):PowerSeries ℤ)=X+X^2+C 2*X^3 := by simp only [map_ofNat];ring
  change mk b*_=_
  rw [h,rhs]
  apply PowerSeries.ext
  intro n
  simp only [map_add,map_sub,coeff_mul_X_pow',coeff_C_mul,coeff_mk,coeff_X,coeff_X_pow,coeff_C]
  by_cases hsmall : n<5
  · interval_cases n <;> norm_num [b,init]
  · simp [b,show n≠0 by omega,show 2≤n by omega,show 4≤n by omega,show ¬n=1 by omega,
      show ¬n=2 by omega,show 3≤n by omega,show n-3≠0 by omega,show n-2≠0 by omega,show n-4≠0 by omega]
    linarith [recurrence n (by omega)]
theorem result : type_of% @OMA.S_oeis_a213243.main := by
  refine ⟨?_,recurrence,series⟩
  intro n hn
  have h : 3*(a n:ℚ)=(2-(-1:ℚ)^n)*((2:ℚ)^n-1) := by exact_mod_cast formula n hn
  linarith
end Deldor14.FiniteCubes
theorem OMA.solution : type_of% @OMA.S_oeis_a213243.main := Deldor14.FiniteCubes.result
