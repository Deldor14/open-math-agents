import OMAStatements.S_oeis_a213245
import Mathlib

namespace Deldor14.FiniteFieldPowers
open OMA.S_oeis_a213245 PowerSeries

noncomputable def powerCount (p : ℕ) [Fact p.Prime] (n d : ℕ) :=
  Nat.card {x : GaloisField p n // x≠0 ∧ ∃ y : GaloisField p n,y^d=x}

private noncomputable def powerEquiv (K : Type*) [Field K] (d : ℕ) (hd : d≠0) :
    (powMonoidHom d : Kˣ →* Kˣ).range ≃ {x : K // x≠0 ∧ ∃ y : K,y^d=x} where
  toFun x := ⟨x.val.val,Units.ne_zero _,by
    obtain ⟨y,hy⟩ := x.property
    exact ⟨y,congrArg Units.val hy⟩⟩
  invFun x := ⟨Units.mk0 x.val x.property.1,by
    obtain ⟨y,hy⟩ := x.property.2
    have yn : y≠0 := by intro h;rw [h,zero_pow hd] at hy;exact x.property.1 hy.symm
    exact ⟨Units.mk0 y yn,Units.ext hy⟩⟩
  left_inv _ := by apply Subtype.ext;apply Units.ext;rfl
  right_inv _ := rfl
theorem cardinal (p : ℕ) [Fact p.Prime] (n d : ℕ) (hn : n≠0) (hd : d≠0) :
    powerCount p n d=(p^n-1)/Nat.gcd (p^n-1) d := by
  let K := GaloisField p n
  have hp := (Fact.out : Nat.Prime p).pos
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [GaloisField.card p n hn];positivity)
  unfold powerCount
  rw [← Nat.card_congr (powerEquiv K d hd),IsCyclic.card_powMonoidHom_range,Nat.card_units,GaloisField.card p n hn]

/-- Counts of nonzero d-th powers over successive extensions have this
recurrence for every period r with d dividing p^r-1. -/
theorem period_recurrence (p : ℕ) [Fact p.Prime] (d r n : ℕ) (hd : 0<d) (hn : 0<n)
    (hr : d ∣ p^r-1) :
    (powerCount p (n+r+r) d:ℤ)=((p:ℤ)^r+1)*powerCount p (n+r) d-(p:ℤ)^r*powerCount p n d := by
  have hp := (Fact.out : Nat.Prime p).pos
  have pos (k : ℕ) : 1≤p^k := Nat.pow_pos hp
  have step (k : ℕ) : (p^(k+r)-1).gcd d=(p^k-1).gcd d := by
    have eq : p^(k+r)-1=(p^k-1)+p^k*(p^r-1) := by
      rw [pow_add,Nat.mul_sub,Nat.mul_one]
      have h := Nat.le_mul_of_pos_right (p^k) (pos r)
      have := pos k
      omega
    rw [eq]
    apply Nat.ModEq.gcd_eq
    simpa using (Nat.ModEq.refl (p^k-1)).add (hr.modEq_zero_nat.mul_left (p^k))
  let g := (p^n-1).gcd d
  have factor (k : ℕ) (hk : 0<k) (hg : (p^k-1).gcd d=g) :
      (g:ℤ)*powerCount p k d=(p:ℤ)^k-1 := by
    have eq := Nat.div_mul_cancel (Nat.gcd_dvd_left (p^k-1) d)
    rw [← cardinal p k d hk.ne' hd.ne',hg,mul_comm] at eq
    have e := congrArg (fun z : ℕ => (z:ℤ)) eq
    push_cast [Nat.cast_sub (pos k)] at e
    exact e
  have f₀ := factor n hn rfl
  have f₁ := factor (n+r) (by omega) (step n)
  have f₂ := factor (n+r+r) (by omega) ((step (n+r)).trans (step n))
  simp only [pow_add] at f₁ f₂
  apply mul_left_cancel₀ (show (g:ℤ)≠0 by exact_mod_cast (Nat.gcd_pos_of_pos_right _ hd).ne')
  linear_combination f₂ - ((p:ℤ)^r+1)*f₁+(p:ℤ)^r*f₀

private theorem recurrence (n : ℕ) (hn : 7≤n) : (a n:ℤ)=9*a (n-3)-8*a (n-6) := by
  obtain ⟨k,rfl⟩ : ∃ k,n=k+7 := ⟨n-7,by omega⟩
  have h := period_recurrence 2 7 3 (k+1) (by decide) (by omega) (by decide)
  have equ (v : ℕ) : powerCount 2 v 7=a v := rfl
  simp only [equ] at h
  rw [show k+1+3+3=k+7 by omega,show k+1+3=k+4 by omega] at h
  rw [show k+7-3=k+4 by omega,show k+7-6=k+1 by omega]
  convert h using 1 <;> norm_num
private theorem series : mk (fun n => if n=0 then (0:ℤ) else a n) *
    ((X-1)*(2*X-1)*(X^2+X+1)*(4*X^2+2*X+1):PowerSeries ℤ) =
      X*(4*X^4+6*X^3+X^2+3*X+1) := by
  let b (n : ℕ) : ℤ := if n=0 then 0 else a n
  have h : mk b*((X-1)*(2*X-1)*(X^2+X+1)*(4*X^2+2*X+1):PowerSeries ℤ) =
      mk b-(C 9*mk b)*X^3+(C 8*mk b)*X^6 := by simp only [map_ofNat];ring
  have rhs : (X*(4*X^4+6*X^3+X^2+3*X+1):PowerSeries ℤ)=X+C 3*X^2+X^3+C 6*X^4+C 4*X^5 := by simp only [map_ofNat];ring
  change mk b*_=_
  rw [h,rhs]
  apply PowerSeries.ext
  intro n
  simp only [map_add,map_sub,coeff_mul_X_pow',coeff_mk,coeff_X,coeff_X_pow,coeff_C_mul,coeff_C]
  by_cases sm : n<7
  · have ev (t : ℕ) (ht : t≠0) : a t=(2^t-1)/Nat.gcd (2^t-1) 7 := cardinal 2 t 7 ht (by decide)
    interval_cases n <;> norm_num [b,ev,Nat.gcd]
  · simp [b,show n≠0 by omega,show 2≤n by omega,show 3≤n by omega,show 4≤n by omega,
      show 5≤n by omega,show 6≤n by omega,show n≠1 by omega,show n≠3 by omega,
      show n-2≠0 by omega,show n-3≠0 by omega,show n-4≠0 by omega,show n-5≠0 by omega,show n-6≠0 by omega]
    linarith [recurrence n (by omega)]
theorem result : type_of% @OMA.S_oeis_a213245.main := ⟨recurrence,series⟩
end Deldor14.FiniteFieldPowers
theorem OMA.solution : type_of% @OMA.S_oeis_a213245.main := Deldor14.FiniteFieldPowers.result
