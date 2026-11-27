import OMAStatements.S_oeis_a192754
import Mathlib

open Polynomial OMA.S_oeis_a192754
namespace Deldor14.Poly192754

noncomputable abbrev M : ℤ[X] := X^2-X-1

theorem monicM : M.Monic := by
  change (X^2-X-1 : ℤ[X]).Monic
  rw [sub_sub]
  apply monic_X_pow_sub
  exact lt_of_le_of_lt (degree_add_le _ _) (by norm_num)

private abbrev f (n : ℕ) : ℤ := 5*(n:ℤ)+1

private theorem degreeM : M.degree=2 := by
  unfold M
  rw [sub_sub,degree_sub_eq_left_of_degree_lt]
  · norm_num
  · exact lt_of_le_of_lt (degree_add_le _ _) (by norm_num)

private theorem xmod : (X : ℤ[X]) %ₘ M = X :=
  (modByMonic_eq_self_iff monicM).mpr (by rw [degreeM]; norm_num)
private theorem cmod (v : ℤ) : (C v : ℤ[X]) %ₘ M = C v :=
  (modByMonic_eq_self_iff monicM).mpr (by rw [degreeM]; exact lt_of_le_of_lt degree_C_le (by norm_num))

private theorem diff (n : ℕ) :
    a (n+2)-a (n+1)-a n=f (n+2)-f (n+1) := by
  have relation : p (n+2)-p (n+1)-p n =
      M*p n + C (f (n+1))*X + C (f (n+2)-f (n+1)) := by
    rw [p.eq_2 (n+1),p.eq_2 n]
    simp only [M,f,map_sub,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
    ring
  have h := congrArg (fun q : ℤ[X] => (q %ₘ M).coeff 0) relation
  simp only [sub_modByMonic,add_modByMonic,self_mul_modByMonic monicM,zero_add,
    ← smul_eq_C_mul,smul_modByMonic,xmod,cmod,coeff_sub,coeff_add,coeff_smul,coeff_C,coeff_X,
    smul_eq_mul] at h
  simpa [a,reduce] using h

private theorem stepA (n : ℕ) : a (n+2)=a (n+1)+a n+5 := by
  have h := diff n
  simp only [f,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at h
  linarith

private theorem base0 : a 0=1 := by
  change ((C 1 : ℤ[X]) %ₘ M).coeff 0 = _
  rw [cmod]; norm_num
private theorem base1 : a 1=6 := by
  change (((X*1+C 6 : ℤ[X]) %ₘ M).coeff 0) = _
  rw [mul_one,add_modByMonic,xmod,cmod]
  norm_num [coeff_X,coeff_C]

private theorem fibForm (n : ℕ) : a n=A000071 (n+3)+4*A000071 (n+2) := by
  unfold A000071
  induction n using Nat.twoStepInduction with
  | zero => norm_num [base0,Nat.fib]
  | one => norm_num [base1,Nat.fib]
  | more n ih jh =>
    have f₂ := Nat.fib_add_two (n := n+2)
    have f₃ := Nat.fib_add_two (n := n+3)
    zify at f₂ f₃
    linarith [stepA n]

private theorem increment (n : ℕ) : a (n+1)-a n=A022095 (n+1) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [base0,base1,A022095]
  | one => norm_num [stepA 0,base0,base1,A022095]
  | more n ih jh =>
    rw [A022095.eq_3 (n+1),Nat.cast_add]
    linarith [stepA n,stepA (n+1)]

private theorem partialSum (n : ℕ) : a n=∑ k ∈ Finset.range (n+1),(A022095 k:ℤ) := by
  induction n with
  | zero => simp [base0,A022095]
  | succ n ih =>
    rw [Finset.sum_range_succ,← ih]
    linarith [increment n]

open PowerSeries in
private theorem series : PowerSeries.mk (fun n => (a n:ℚ))=G := by
  let s := PowerSeries.mk (fun n => (a n:ℚ))
  let den : PowerSeries ℚ := (PowerSeries.X-1)*(PowerSeries.X^2+PowerSeries.X-1)
  have inverse : den*den⁻¹=1 := PowerSeries.mul_inv_cancel den (by simp [den])
  have eq : s*den=1+4*PowerSeries.X := by
    have lhs : s*den = s*PowerSeries.X^3 - (PowerSeries.C (2:ℚ)*s)*PowerSeries.X + s := by
      simp only [den,map_ofNat]; ring
    have rhs : (1+4*PowerSeries.X : PowerSeries ℚ) = PowerSeries.C (1:ℚ)+PowerSeries.C (4:ℚ)*PowerSeries.X^1 := by simp [map_ofNat]
    rw [lhs,rhs]
    apply PowerSeries.ext
    intro n
    have shift (b : PowerSeries ℚ) : PowerSeries.coeff n (b*PowerSeries.X) =
        if 1≤n then PowerSeries.coeff (n-1) b else 0 := by simpa only [pow_one] using PowerSeries.coeff_mul_X_pow' b 1 n
    simp only [map_add,map_sub,PowerSeries.coeff_C_mul_X_pow,PowerSeries.coeff_mul_X_pow',shift,PowerSeries.coeff_C_mul,s,PowerSeries.coeff_mk,PowerSeries.coeff_C]
    by_cases small : n<3
    · interval_cases n <;> norm_num [base0,base1,stepA 0]
    · obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
      have h : a (k+3)-2*a (k+2)+a k=0 := by linarith [stepA (k+1),stepA k]
      have h' : (a (k+3):ℚ)-2*a (k+2)+a k=0 := by exact_mod_cast h
      simp [show k+3-1=k+2 by omega]
      linarith
  change s=(1+4*PowerSeries.X)*den⁻¹
  rw [← eq,mul_assoc,inverse,mul_one]

theorem result : type_of% @OMA.S_oeis_a192754.main := ⟨series,partialSum,fibForm⟩
end Deldor14.Poly192754

theorem OMA.solution : type_of% @OMA.S_oeis_a192754.main := Deldor14.Poly192754.result
